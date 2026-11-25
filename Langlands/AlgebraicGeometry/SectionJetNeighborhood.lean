import Langlands.AlgebraicGeometry.KernelFlatBaseChange
import Langlands.AlgebraicGeometry.SectionJetAffineNeighborhood
import Langlands.GroupScheme.IdentityJetBaseChange

/-! # Uniform finite-jet detection near a smooth section -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

private theorem exists_sectionCharts {S X : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) (x : S) :
    ∃ (U : S.affineOpens) (V : X.affineOpens),
      x ∈ U.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 ∧ e ⁻¹ᵁ V.1 = U.1 := by
  obtain ⟨U₀, hU₀, hxU₀, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have hx' : e x ∈ f ⁻¹ᵁ U₀ := by
    change f (e x) ∈ U₀
    rw [← Scheme.Hom.comp_apply, he]
    exact hxU₀
  obtain ⟨V₀, hV₀, hxV₀, hV₀U₀⟩ := exists_isAffineOpen_mem_and_subset hx'
  obtain ⟨r, hr, hxr⟩ := hU₀.exists_basicOpen_le (V := e ⁻¹ᵁ V₀) ⟨x, hxV₀⟩ hxU₀
  let U := S.basicOpen r
  let V := X.basicOpen (f.appLE U₀ V₀ hV₀U₀ r)
  have hV : V = V₀ ⊓ f ⁻¹ᵁ U := Scheme.basicOpen_appLE _ _ _ _ _
  refine ⟨⟨U, hU₀.basicOpen r⟩, ⟨V, hV₀.basicOpen _⟩, hxr, hV.trans_le inf_le_right, ?_⟩
  change e ⁻¹ᵁ V = U
  rw [hV, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, he, Scheme.Hom.id_preimage]
  exact inf_eq_right.mpr hr

private theorem resLE_section_ker {S X : Scheme.{u}} (e : S ⟶ X) [QuasiCompact e]
    (U : S.Opens) (V : X.Opens) (hUV : e ⁻¹ᵁ V = U) :
    (e.resLE V U (le_of_eq hUV.symm)).ker = e.ker.comap V.ι := by
  subst U
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (KernelFlatBaseChange.ker_comap_of_isPullback_of_isOpenImmersion e
    (e ∣_ V) (e ⁻¹ᵁ V).ι V.ι (isPullback_morphismRestrict e V)).symm

private theorem resLE_section_comp {S X : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) {U : S.Opens} {V : X.Opens}
    (hVU : V ≤ f ⁻¹ᵁ U) (hUV : e ⁻¹ᵁ V = U) :
    e.resLE V U (le_of_eq hUV.symm) ≫ f.resLE U V hVU = 𝟙 U.toScheme := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, he, Category.comp_id, Category.id_comp]

/-- Order `n` detects vanishing near the section on all tests if the extended
ideal vanishes locally at every point of the changed section whenever it is
contained in the extension of the `(n + 1)`st power of the section ideal. -/
def DetectsVanishingNearSection {S X : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) (J : X.IdealSheafData) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) (b : T ⟶ S),
    let p := pullback.snd b f
    let eT := pullback.lift (𝟙 T) (b ≫ e)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
    J.comap p ≤ (e.ker ^ (n + 1)).comap p →
    ∀ t : T, ∃ W : (pullback b f).Opens, eT t ∈ W ∧ J ≤ (W.ι ≫ p).ker

/-- The kernel ideal of a locally finitely presented closed immersion is
finitely generated on every affine chart. -/
theorem fg_ideal_ker_of_locallyOfFinitePresentation {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] [LocallyOfFinitePresentation j] (V : X.affineOpens) :
    (j.ker.ideal V).FG := by
  rw [Scheme.Hom.ker_apply]
  let : Algebra Γ(X, V.1) Γ(Y, j ⁻¹ᵁ V.1) := (j.app V.1).hom.toAlgebra
  have hFP : (j.appLE V.1 (j ⁻¹ᵁ V.1) le_rfl).hom.FinitePresentation :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) j inferInstance V
      ⟨_, V.2.preimage j⟩ le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hFP
  let : Algebra.FinitePresentation Γ(X, V.1) Γ(Y, j ⁻¹ᵁ V.1) := hFP
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(X, V.1) Γ(Y, j ⁻¹ᵁ V.1)) (j.app_surjective V.1 V.2)

set_option maxHeartbeats 650000 in
private theorem chart_neighborhood
    {S X : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    [QuasiCompact e] (J : X.IdealSheafData)
    (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (hUV : e ⁻¹ᵁ V = U)
    {n N : ℕ} (hnN : n ≤ N)
    (hn : DetectsVanishingNearSectionAffine (f.resLE U V hVU)
      (e.resLE V U (le_of_eq hUV.symm))
      (resLE_section_comp f e he hVU hUV)
      (J.comap V.ι) n)
    (T : Scheme.{u}) (b : T ⟶ S)
    (hJet : J.comap (pullback.snd b f) ≤ (e.ker ^ (N + 1)).comap (pullback.snd b f))
    (t : T) (ht : b t ∈ U) :
    ∃ W : (pullback b f).Opens,
      (pullback.lift (𝟙 T) (b ≫ e)
        (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])) t ∈ W ∧
      J ≤ (W.ι ≫ pullback.snd b f).ker := by
  let q := f.resLE U V hVU
  let s := e.resLE V U (le_of_eq hUV.symm)
  obtain ⟨A, hA, hta, hAU⟩ := exists_isAffineOpen_mem_and_subset
    (show t ∈ b ⁻¹ᵁ U from ht)
  let : IsAffine A.toScheme := hA
  let a := b.resLE U A hAU
  let p := pullback.snd b f
  let p' := pullback.snd a q
  let j := pullback.map a q b f A.ι V.ι U.ι
    (Scheme.Hom.resLE_comp_ι b hAU) (Scheme.Hom.resLE_comp_ι f hVU)
  have : IsOpenImmersion j := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  have hj : j ≫ p = p' ≫ V.ι := pullback.lift_snd _ _ _
  have hle : e.ker ^ (N + 1) ≤ e.ker ^ (n + 1) :=
    pow_le_pow_right_of_le_one' (by rw [Scheme.IdealSheafData.one_eq_top]; exact le_top)
      (Nat.succ_le_succ hnN)
  have hJet' : (J.comap V.ι).comap p' ≤ (s.ker ^ (n + 1)).comap p' := by
    rw [resLE_section_ker e U V hUV, ← Langlands.GroupScheme.IdentityJet.idealSheaf_comap_pow,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← hj,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono j
      (hJet.trans (Scheme.IdealSheafData.comap_mono p hle))
  obtain ⟨W, hW, hJW⟩ := hn A.toScheme a hJet'
  let eT : T ⟶ pullback b f := pullback.lift (𝟙 T) (b ≫ e)
    (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  have hsq : s ≫ q = 𝟙 _ := resLE_section_comp f e he hVU hUV
  let eA : A.toScheme ⟶ pullback a q := pullback.lift (𝟙 A.toScheme) (a ≫ s)
    (by rw [Category.id_comp, Category.assoc, hsq, Category.comp_id])
  have heA : eA ≫ j = A.ι ≫ eT := by
    apply pullback.hom_ext
    · simp [eA, eT, j]
    · change (eA ≫ j) ≫ p = (A.ι ≫ eT) ≫ p
      rw [Category.assoc, hj, ← Category.assoc, Category.assoc A.ι]
      change (eA ≫ pullback.snd a q) ≫ V.ι = A.ι ≫ eT ≫ pullback.snd b f
      rw [pullback.lift_snd, pullback.lift_snd, Category.assoc]
      change a ≫ (e.resLE V U (le_of_eq hUV.symm) ≫ V.ι) = A.ι ≫ b ≫ e
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  refine ⟨j ''ᵁ W, ?_, ?_⟩
  · refine ⟨eA ⟨t, hta⟩, hW (Set.mem_range_self _), ?_⟩
    change j (eA ⟨t, hta⟩) = eT t
    exact congrArg (fun g : A.toScheme ⟶ pullback b f => g ⟨t, hta⟩) heA
  · have hJ' : J ≤ (W.ι ≫ p' ≫ V.ι).ker := by
      rw [← Category.assoc, Scheme.Hom.ker_comp]
      exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr hJW
    rw [← j.isoImage_inv_ι W, Category.assoc, Category.assoc, hj]
    exact hJ'.trans (Scheme.Hom.le_ker_comp _ _)

set_option maxHeartbeats 650000 in
/-- Over a quasi-compact base one order works in every base change, even when
the smooth source is covered by several affine charts. -/
theorem exists_order_of_vanishing_near_section
    {S X : Scheme.{u}} [CompactSpace S] (f : X ⟶ S) [Smooth f]
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) [QuasiCompact e] (J : X.IdealSheafData)
    (hJ : ∀ V : X.affineOpens, (J.ideal V).FG) :
    ∃ N, DetectsVanishingNearSection f e he J N := by
  classical
  choose U V hx hVU hUV using exists_sectionCharts f e he
  have hOrders (x : S) :
      ∃ n, DetectsVanishingNearSectionAffine (f.resLE (U x).1 (V x).1 (hVU x))
        (e.resLE (V x).1 (U x).1 (le_of_eq (hUV x).symm))
        (resLE_section_comp f e he (hVU x) (hUV x))
        (J.comap (V x).1.ι) n := by
    let : IsAffine (U x).1.toScheme := (U x).2
    let : IsAffine (V x).1.toScheme := (V x).2
    apply exists_order_of_vanishing_near_section_affine
    rw [Scheme.IdealSheafData.ideal_comap_of_le J (V x).1.ι (V x)
      ⟨⊤, isAffineOpen_top _⟩ (by simp)]
    exact (hJ (V x)).map _
  choose n hn using hOrders
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U x).1 : Set S)) (fun x => (U x).1.isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let N := F.sup n
  refine ⟨N, fun T b hJet t => ?_⟩
  obtain ⟨x, hxF, hxt⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ (b t)))
  exact chart_neighborhood f e he J (U x).1 (V x).1 (hVU x) (hUV x)
    (Finset.le_sup (f := n) hxF) (hn x) T b hJet t hxt

end Langlands.AlgebraicGeometry
