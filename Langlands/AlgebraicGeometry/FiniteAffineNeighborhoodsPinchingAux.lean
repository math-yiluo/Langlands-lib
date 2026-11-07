import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPushoutStatement

/-! # Finite-point avoidance for affine pinching -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry

private theorem exists_mem_all_not_mem_prime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (S : Finset (Ideal R)) (hS : ∀ J ∈ S, ¬ J ≤ p) :
    ∃ x : R, (∀ J ∈ S, x ∈ J) ∧ x ∉ p := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, p.one_notMem⟩
  | @insert J S hJS ih =>
      obtain ⟨a, haJ, hap⟩ := SetLike.not_le_iff_exists.mp (hS J (by simp))
      obtain ⟨b, hbS, hbp⟩ := ih (fun K hK => hS K (by simp [hK]))
      refine ⟨a * b, ?_, (Ideal.IsPrime.mul_notMem inferInstance hap hbp)⟩
      intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · exact K.mul_mem_right b haJ
      · exact K.mul_mem_left a (hbS K hK)

/-- A prescribed residue class modulo an ideal admits a representative avoiding
any finite family of primes which do not contain that ideal. -/
theorem exists_add_mem_ideal_avoiding
    {R : Type u} [CommRing R] (I : Ideal R) (E : Finset (PrimeSpectrum R))
    (hI : ∀ p ∈ E, ¬ I ≤ p.asIdeal) (v : R) :
    ∃ a ∈ I, ∀ p ∈ E, v + a ∉ p.asIdeal := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | @insert p E hpE ih =>
      obtain ⟨a, haI, haE⟩ := ih (fun q hq => hI q (by simp [hq]))
      by_cases hp : v + a ∈ p.asIdeal
      · obtain ⟨c, hcI, hcp⟩ := SetLike.not_le_iff_exists.mp (hI p (by simp))
        let S : Finset (Ideal R) :=
          (E.filter (fun q => ¬ q.asIdeal ≤ p.asIdeal)).image PrimeSpectrum.asIdeal
        have hS : ∀ J ∈ S, ¬ J ≤ p.asIdeal := by
          intro J hJ
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hJ
          exact (Finset.mem_filter.mp hq).2
        obtain ⟨b, hbS, hbp⟩ := exists_mem_all_not_mem_prime p.asIdeal S hS
        have hcbp : c * b ∉ p.asIdeal := p.isPrime.mul_notMem hcp hbp
        have hnew : v + (a + c * b) ∉ p.asIdeal := by
          rw [← add_assoc]
          exact fun h => hcbp ((p.asIdeal.add_mem_iff_right hp).mp h)
        refine ⟨a + c * b, I.add_mem haI (I.mul_mem_right b hcI), ?_⟩
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hnew
        · by_cases hqp : q.asIdeal ≤ p.asIdeal
          · exact fun h => hnew (hqp h)
          · have hbq : b ∈ q.asIdeal :=
              hbS _ (Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hqp⟩, rfl⟩)
            rw [← add_assoc]
            exact fun h => haE q hq
              ((q.asIdeal.add_mem_iff_left (q.asIdeal.mul_mem_left c hbq)).mp h)
      · exact ⟨a, haI, fun q hq => (Finset.mem_insert.mp hq).elim (fun h => h ▸ hp)
          (haE q)⟩

/-- A section on a closed subscheme of an affine scheme lifts to a section
nonvanishing at any prescribed finite set outside that closed subscheme. -/
theorem exists_section_lift_avoiding
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (E : Set X) (hE : E.Finite) (hEZ : Disjoint E (Set.range i))
    (t : Γ(Z, ⊤)) :
    ∃ s : Γ(X, ⊤), i.appTop s = t ∧ E ⊆ X.basicOpen s := by
  classical
  let : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  have hsurj : Function.Surjective i.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  let F : Set (PrimeSpectrum Γ(X, ⊤)) := X.toSpecΓ '' E
  have hF : F.Finite := hE.image X.toSpecΓ
  have hker : ∀ p ∈ hF.toFinset, ¬ RingHom.ker i.appTop.hom ≤ p.asIdeal := by
    intro p hp hle
    obtain ⟨x, hx, rfl⟩ := hF.mem_toFinset.mp hp
    have hmem : X.toSpecΓ x ∈ Set.range (PrimeSpectrum.comap i.appTop.hom) := by
      rw [range_comap_of_surjective (R := Γ(X, ⊤)) (S := Γ(Z, ⊤)) i.appTop.hom hsurj]
      exact hle
    obtain ⟨q, hq⟩ := hmem
    have heq : i (Z.isoSpec.inv q) = x := by
      have he := congrArg (fun f : Spec Γ(Z, ⊤) ⟶ X => f q)
        (Scheme.isoSpec_inv_naturality i)
      calc
        i (Z.isoSpec.inv q) = (Z.isoSpec.inv ≫ i) q :=
          (Scheme.Hom.comp_apply _ _ _).symm
        _ = (Spec.map i.appTop ≫ X.isoSpec.inv) q := he.symm
        _ = X.isoSpec.inv (PrimeSpectrum.comap i.appTop.hom q) :=
          Scheme.Hom.comp_apply _ _ _
        _ = X.isoSpec.inv (X.toSpecΓ x) := congrArg X.isoSpec.inv hq
        _ = x := by
          change (X.toSpecΓ ≫ X.isoSpec.inv) x = x
          rw [Scheme.toSpecΓ_isoSpec_inv]
          rfl
    exact Set.disjoint_left.mp hEZ hx ⟨Z.isoSpec.inv q, heq⟩
  obtain ⟨v, hv⟩ := hsurj t
  obtain ⟨a, ha, havoid⟩ := exists_add_mem_ideal_avoiding
    (RingHom.ker i.appTop.hom) hF.toFinset hker v
  refine ⟨v + a, ?_, ?_⟩
  · simp [map_add, hv, RingHom.mem_ker.mp ha]
  · intro x hx
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact havoid (X.toSpecΓ x) (hF.mem_toFinset.mpr ⟨x, hx, rfl⟩)

/-- Finite-point prime avoidance inside an affine open of an arbitrary scheme. -/
theorem exists_basicOpen_of_finite_in_affineOpen
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (E : Set X) (hE : E.Finite) (hEU : E ⊆ U)
    (W : X.Opens) (hEW : E ⊆ W) :
    ∃ s : Γ(X, U), E ⊆ X.basicOpen s ∧ X.basicOpen s ≤ W := by
  let : IsAffine U.toScheme := hU
  have hE' : (U.ι ⁻¹' E).Finite :=
    hE.preimage U.ι.isOpenEmbedding.injective.injOn
  obtain ⟨s, hsE, hsW⟩ := GenericPointAvoidance.exists_basicOpen_of_finite
    hE' (W := U.ι ⁻¹ᵁ W) (fun _ hx => hEW hx)
  have himage : U.ι ''ᵁ U.toScheme.basicOpen s = X.basicOpen (U.topIso.hom s) := by
    have hc : U.topIso.inv (U.topIso.hom s) = s := by
      change (U.topIso.hom ≫ U.topIso.inv) s = s
      rw [U.topIso.hom_inv_id]
      rfl
    have h := U.ι_image_basicOpen_topIso_inv (U.topIso.hom s)
    rw [hc] at h
    exact h
  refine ⟨U.topIso.hom s, ?_, ?_⟩
  · intro x hx
    rw [← himage]
    exact ⟨⟨x, hEU hx⟩, hsE hx, rfl⟩
  · rw [← himage]
    rintro _ ⟨x, hx, rfl⟩
    exact hsW hx

/-- Lift a principal open on the closed intersection with an affine open,
while retaining a finite set outside the closed subscheme. -/
theorem exists_affineOpen_lift_basicOpen
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U)
    (E : Set X) (hE : E.Finite) (hEU : E ⊆ U)
    (hEZ : Disjoint E (Set.range i)) (t : Γ(Z, i ⁻¹ᵁ U)) :
    ∃ V : X.Opens, IsAffineOpen V ∧ E ⊆ V ∧ V ≤ U ∧
      i ⁻¹ᵁ V = Z.basicOpen t := by
  let : IsAffine U.toScheme := hU
  have hE' : (U.ι ⁻¹' E).Finite :=
    hE.preimage U.ι.isOpenEmbedding.injective.injOn
  have hEZ' : Disjoint (U.ι ⁻¹' E) (Set.range (i ∣_ U)) := by
    refine Set.disjoint_left.mpr ?_
    rintro x hx ⟨z, rfl⟩
    exact Set.disjoint_left.mp hEZ hx
      ⟨z.val, (morphismRestrict_base_coe i U z).symm⟩
  obtain ⟨s, hs, hEs⟩ := exists_section_lift_avoiding
    (i ∣_ U) (U.ι ⁻¹' E) hE' hEZ' ((i ⁻¹ᵁ U).topIso.inv t)
  let V : X.Opens := U.ι ''ᵁ U.toScheme.basicOpen s
  refine ⟨V, ((isAffineOpen_top U.toScheme).basicOpen s).image_of_isOpenImmersion U.ι,
    ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hEU hx⟩, hEs hx, rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · dsimp only [V]
    rw [← image_morphismRestrict_preimage, Scheme.preimage_basicOpen_top, hs,
      Scheme.Opens.ι_image_basicOpen_topIso_inv]

/-- For finite pinching of AF schemes, finite sets on the two sides admit
affine neighborhoods with exactly the same inverse image on the conductor. -/
theorem exists_compatible_affineOpens_of_finite
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsFinite j]
    (hX : PointTopology.HasFiniteAffineNeighborhoods X)
    (hY : PointTopology.HasFiniteAffineNeighborhoods Y)
    (E : Set X) (F : Set Y) (hE : E.Finite) (hF : F.Finite)
    (hEZ : Disjoint E (Set.range i)) :
    ∃ U : X.affineOpens, ∃ V : Y.affineOpens,
      E ⊆ U.1 ∧ F ⊆ V.1 ∧ i ⁻¹ᵁ U.1 = j ⁻¹ᵁ V.1 := by
  have hFZ : (j ⁻¹' F).Finite := j.finite_preimage hF
  obtain ⟨U₀, hU₀⟩ := hX (E ∪ i '' (j ⁻¹' F)) (hE.union (hFZ.image i))
  obtain ⟨V₀, hV₀⟩ := hY F hF
  have hEU₀ : E ⊆ U₀.1 := fun x hx => hU₀ (Or.inl hx)
  have hFZU₀ : j ⁻¹' F ⊆ i ⁻¹ᵁ U₀.1 :=
    fun z hz => hU₀ (Or.inr ⟨z, hz, rfl⟩)
  obtain ⟨t, hFt, htV₀⟩ := exists_basicOpen_of_finite_in_affineOpen
    (i ⁻¹ᵁ U₀.1) (U₀.2.preimage i) (j ⁻¹' F) hFZ hFZU₀
    (j ⁻¹ᵁ V₀.1) (fun z hz => hV₀ hz)
  obtain ⟨U₁, hU₁, hEU₁, _, hT₁⟩ := exists_affineOpen_lift_basicOpen
    i U₀.1 U₀.2 E hE hEU₀ hEZ t
  have hT₁V₀ : i ⁻¹ᵁ U₁ ≤ j ⁻¹ᵁ V₀.1 := by
    rw [hT₁]
    exact htV₀
  have hFZU₁ : j ⁻¹' F ⊆ i ⁻¹ᵁ U₁ := by
    rw [hT₁]
    exact hFt
  let W : Y.Opens :=
    ⟨(j '' ((i ⁻¹ᵁ U₁ : Z.Opens) : Set Z)ᶜ)ᶜ,
      (j.isClosedMap _ (i ⁻¹ᵁ U₁).2.isClosed_compl).isOpen_compl⟩
  have hFW : F ⊆ W := by
    rintro y hy ⟨z, hz, rfl⟩
    exact hz (hFZU₁ hy)
  have hWT₁ : j ⁻¹ᵁ W ≤ i ⁻¹ᵁ U₁ := by
    intro z hz
    by_contra hz'
    exact hz ⟨z, hz', rfl⟩
  obtain ⟨s, hFs, hsW⟩ := exists_basicOpen_of_finite_in_affineOpen
    V₀.1 V₀.2 F hF hV₀ W hFW
  have hsT₁ : j ⁻¹ᵁ Y.basicOpen s ≤ i ⁻¹ᵁ U₁ :=
    (j.preimage_mono hsW).trans hWT₁
  obtain ⟨U, hU, hEU, _, hTU⟩ := exists_affineOpen_lift_basicOpen
    i U₁ hU₁ E hE hEU₁ hEZ (j.appLE V₀.1 (i ⁻¹ᵁ U₁) hT₁V₀ s)
  refine ⟨⟨U, hU⟩, ⟨Y.basicOpen s, V₀.2.basicOpen s⟩, hEU, hFs, ?_⟩
  rw [hTU, Scheme.basicOpen_appLE, inf_eq_right.mpr hsT₁]

end Langlands.AlgebraicGeometry
