import Mathlib
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions
import Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof
import Langlands.Algebra.SmoothEqualizerFibreCriterionProof

/-! # Proof of relative global functions for smooth proper morphisms -/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-- If `p.app V` is an isomorphism for every affine open `V` of the target, then `p.app U`
is an isomorphism for every open `U`. -/
theorem isIso_app_of_forall_isAffineOpen {X S : Scheme.{u}} (p : X ⟶ S)
    (h : ∀ V : S.Opens, IsAffineOpen V → IsIso (p.app V)) (U : S.Opens) :
    IsIso (p.app U) := by
  have hbij : ∀ V : S.Opens, IsAffineOpen V → Function.Bijective (p.app V) := fun V hV ↦
    (ConcreteCategory.isIso_iff_bijective _).mp (h V hV)
  have hstalk : ∀ x : S, Function.Injective
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.c) := fun x ↦
    TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis S.isBasis_affineOpens
      (fun V hV ↦ (hbij V hV).1) x
  let G : TopCat.Sheaf CommRingCat S :=
    ⟨p.base _* X.presheaf, TopCat.Sheaf.pushforward_sheaf_of_sheaf _ X.IsSheaf⟩
  let φ : S.sheaf ⟶ G := ObjectProperty.homMk p.c
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := S.sheaf)
      (G := p.base _* X.presheaf) p.c U fun x _ ↦ hstalk x
  · refine TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective φ U
      (fun x _ ↦ hstalk x) fun t x hx ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    obtain ⟨s, hs⟩ := (hbij V hV).2 (G.1.map (homOfLE hVU).op t)
    exact ⟨V, hxV, homOfLE hVU, s, hs⟩

lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

section Fibre

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)

/-- The ring map `R → Γ(X, W)` induced by `p`. -/
noncomputable def secHom (W : X.Opens) : R ⟶ Γ(X, W) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ W (le_top.trans_eq p.preimage_top.symm)

set_option backward.isDefEq.respectTransparency false in
lemma secHom_map {W W' : X.Opens} (h : W' ≤ W) :
    secHom p W ≫ X.presheaf.map (homOfLE h).op = secHom p W' := by
  rw [secHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl

variable (K : Type u) [Field K] [Algebra R K]

/-- The structure morphism `Spec K ⟶ Spec R`. -/
noncomputable abbrev fibreMap : Spec (CommRingCat.of K) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The ring map `K → Γ(X_K, g⁻¹ W)` on the fibre `X_K = X ×_{Spec R} Spec K`. -/
noncomputable def fibreSec (W : X.Opens) :
    CommRingCat.of K ⟶ Γ(pullback p (fibreMap K), pullback.fst p (fibreMap K) ⁻¹ᵁ W) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (pullback.snd p (fibreMap K)).appLE ⊤ _ (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)

set_option backward.isDefEq.respectTransparency false in
lemma fibreSec_w (W : X.Opens) :
    CommRingCat.ofHom (algebraMap R K) ≫ fibreSec p K W =
      secHom p W ≫ (pullback.fst p (fibreMap K)).appLE W _ le_rfl := by
  rw [fibreSec, Scheme.ΓSpecIso_inv_naturality_assoc, secHom, Category.assoc]
  congr 1
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom pullback.condition, Scheme.Hom.comp_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma fibreSec_map {W W' : X.Opens} (h : W' ≤ W) :
    fibreSec p K W ≫ (pullback p (fibreMap K)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ h)).op = fibreSec p K W' := by
  rw [fibreSec, Category.assoc, Scheme.Hom.appLE_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open `W` of `X`, the square of section rings of the fibre square is a pushout. -/
lemma isPushout_fibre {W : X.Opens} (hW : IsAffineOpen W) :
    IsPushout (CommRingCat.ofHom (algebraMap R K)) (secHom p W) (fibreSec p K W)
      ((pullback.fst p (fibreMap K)).appLE W _ le_rfl) := by
  have H := IsPullback.of_hasPullback p (fibreMap K)
  have hUY : pullback.fst p (fibreMap K) ⁻¹ᵁ W =
      pullback.fst p (fibreMap K) ⁻¹ᵁ W ⊓ pullback.snd p (fibreMap K) ⁻¹ᵁ ⊤ := by simp
  have h3 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ hUY (isAffineOpen_top _) (isAffineOpen_top _) hW)
  refine h3.flip.of_iso' (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso (CommRingCat.of K)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.Hom.appLE]; rfl
  · simp [secHom]
  · simp [fibreSec]
  · simp

section Tensor

variable [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halg : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom p W).hom)

/-- The restriction map `Γ(X, W) → Γ(X, W')` as an `R`-algebra homomorphism. -/
noncomputable def resAlgHom {W W' : X.Opens} (h : W' ≤ W) : Γ(X, W) →ₐ[R] Γ(X, W') :=
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r ↦ by
      change (X.presheaf.map (homOfLE h).op).hom (algebraMap R Γ(X, W) r) = _
      rw [halg, halg, ← CommRingCat.comp_apply, secHom_map] }

lemma resAlgHom_apply {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, W)) :
    resAlgHom p halg h c = (X.presheaf.map (homOfLE h).op).hom c := rfl

/-- The canonical map `K ⊗[R] Γ(X, W) → Γ(X_K, g⁻¹ W)`. -/
noncomputable def fibreTensor (W : X.Opens) :
    CommRingCat.of (K ⊗[R] Γ(X, W)) ⟶
      Γ(pullback p (fibreMap K), pullback.fst p (fibreMap K) ⁻¹ᵁ W) :=
  (CommRingCat.isPushout_tensorProduct R K Γ(X, W)).desc (fibreSec p K W)
    ((pullback.fst p (fibreMap K)).appLE W _ le_rfl) (by
      refine (fibreSec_w p K W).trans ?_
      congr 1
      ext x
      exact congr($(halg W) x).symm)

lemma fibreTensor_tmul (W : X.Opens) (k : K) (c : Γ(X, W)) :
    (fibreTensor p K halg W).hom (k ⊗ₜ c) =
      (fibreSec p K W).hom k * ((pullback.fst p (fibreMap K)).appLE W _ le_rfl).hom c := by
  have e : (k ⊗ₜ[R] c : K ⊗[R] Γ(X, W)) =
      Algebra.TensorProduct.includeLeftRingHom k * Algebra.TensorProduct.includeRight c := by
    simp
  rw [e, map_mul]
  congr 1
  · exact congr($((CommRingCat.isPushout_tensorProduct R K Γ(X, W)).inl_desc _ _ _).hom k)
  · exact congr($((CommRingCat.isPushout_tensorProduct R K Γ(X, W)).inr_desc _ _ _).hom c)

lemma fibreTensor_map {W W' : X.Opens} (h : W' ≤ W) (x : K ⊗[R] Γ(X, W)) :
    ((pullback p (fibreMap K)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom ((fibreTensor p K halg W).hom x) =
      (fibreTensor p K halg W').hom
        (Algebra.TensorProduct.map (AlgHom.id R K) (resAlgHom p halg h) x) := by
  induction x with
  | tmul k c =>
    rw [Algebra.TensorProduct.map_tmul, fibreTensor_tmul, fibreTensor_tmul, map_mul,
      AlgHom.id_apply, resAlgHom_apply, ← CommRingCat.comp_apply, fibreSec_map p K h,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
      Scheme.Hom.map_appLE]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma fibreTensor_injective {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Injective (fibreTensor p K halg W).hom := by
  have e : CommRingCat.ofHom (algebraMap R Γ(X, W)) = secHom p W := by
    rw [halg]; rfl
  have h : IsPushout (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (algebraMap R Γ(X, W))) (fibreSec p K W)
      ((pullback.fst p (fibreMap K)).appLE W _ le_rfl) := by
    rw [e]; exact isPushout_fibre p K hW
  have h1 := CommRingCat.isPushout_tensorProduct R K Γ(X, W)
  have : (h1.isoIsPushout _ _ h).hom = fibreTensor p K halg W :=
    h1.hom_ext (by simp [fibreTensor]) (by simp [fibreTensor])
  rw [← this]
  exact (h1.isoIsPushout _ _ h).commRingCatIsoToRingEquiv.injective

end Tensor

end Fibre

section Cech

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)

lemma smooth_secHom [Smooth p] {W : X.Opens} (hW : IsAffineOpen W) :
    (secHom p W).hom.Smooth :=
  RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appLE @Smooth p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ _)

lemma secHom_apply (W : X.Opens) (a : Γ(Spec R, ⊤)) :
    (secHom p W).hom ((Scheme.ΓSpecIso R).hom a) =
      (X.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom a) := by
  rw [secHom, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  rfl

variable [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halg : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom p W).hom)
  {ι : Type u} (U : ι → X.Opens)

/-- The first Čech coface map `∏ Γ(X, U i) → ∏ Γ(X, U i ⊓ U j)`. -/
noncomputable def cechLeft : (∀ i, Γ(X, U i)) →ₐ[R] ∀ ij : ι × ι, Γ(X, U ij.1 ⊓ U ij.2) :=
  AlgHom.pi fun ij ↦ (resAlgHom p halg inf_le_left).comp (Pi.evalAlgHom R (fun i ↦ Γ(X, U i)) ij.1)

/-- The second Čech coface map `∏ Γ(X, U i) → ∏ Γ(X, U i ⊓ U j)`. -/
noncomputable def cechRight : (∀ i, Γ(X, U i)) →ₐ[R] ∀ ij : ι × ι, Γ(X, U ij.1 ⊓ U ij.2) :=
  AlgHom.pi fun ij ↦
    (resAlgHom p halg inf_le_right).comp (Pi.evalAlgHom R (fun i ↦ Γ(X, U i)) ij.2)

variable (K : Type u) [Field K] [Algebra R K]

/-- The `i`-th component `K ⊗[R] ∏ Γ(X, U i) → Γ(X_K, g⁻¹ U i)`. -/
noncomputable def fibreComp (i : ι) :
    K ⊗[R] (∀ i, Γ(X, U i)) →+*
      Γ(pullback p (fibreMap K), pullback.fst p (fibreMap K) ⁻¹ᵁ U i) :=
  (fibreTensor p K halg (U i)).hom.comp
    (Algebra.TensorProduct.map (AlgHom.id R K) (Pi.evalAlgHom R (fun i ↦ Γ(X, U i)) i)).toRingHom

lemma piRight_apply_eq [Fintype ι] [DecidableEq ι] (z : K ⊗[R] (∀ i, Γ(X, U i))) (i : ι) :
    Algebra.TensorProduct.piRight R R K (fun i ↦ Γ(X, U i)) z i =
      Algebra.TensorProduct.map (AlgHom.id R K) (Pi.evalAlgHom R (fun i ↦ Γ(X, U i)) i) z := by
  induction z with
  | tmul k c => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

lemma fibreComp_injective [Finite ι] (hU : ∀ i, IsAffineOpen (U i)) :
    Function.Injective fun z i ↦ fibreComp p halg U K i z := by
  classical
  have := Fintype.ofFinite ι
  intro z z' h
  apply (Algebra.TensorProduct.piRight R R K (fun i ↦ Γ(X, U i))).injective
  funext i
  rw [piRight_apply_eq, piRight_apply_eq]
  exact fibreTensor_injective p K halg (hU i) (congr_fun h i)

lemma fibreComp_algebraMap (i : ι) (k : K) :
    fibreComp p halg U K i (algebraMap K (K ⊗[R] (∀ i, Γ(X, U i))) k) =
      (fibreSec p K (U i)).hom k := by
  rw [Algebra.TensorProduct.algebraMap_apply, fibreComp, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
    fibreTensor_tmul, map_one, mul_one]
  rfl

lemma fibreComp_cechLeft (x : K ⊗[R] (∀ i, Γ(X, U i))) (i j : ι) :
    ((pullback p (fibreMap K)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op).hom (fibreComp p halg U K i x) =
    (fibreTensor p K halg (U i ⊓ U j)).hom
      (Algebra.TensorProduct.map (AlgHom.id R K)
        (Pi.evalAlgHom R (fun ij : ι × ι ↦ Γ(X, U ij.1 ⊓ U ij.2)) (i, j))
        (Algebra.TensorProduct.map (AlgHom.id R K) (cechLeft p halg U) x)) := by
  rw [fibreComp, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    fibreTensor_map p K halg inf_le_left]
  congr 1
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp]
  rfl

lemma fibreComp_cechRight (x : K ⊗[R] (∀ i, Γ(X, U i))) (i j : ι) :
    ((pullback p (fibreMap K)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ inf_le_right)).op).hom (fibreComp p halg U K j x) =
    (fibreTensor p K halg (U i ⊓ U j)).hom
      (Algebra.TensorProduct.map (AlgHom.id R K)
        (Pi.evalAlgHom R (fun ij : ι × ι ↦ Γ(X, U ij.1 ⊓ U ij.2)) (i, j))
        (Algebra.TensorProduct.map (AlgHom.id R K) (cechRight p halg U) x)) := by
  rw [fibreComp, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    fibreTensor_map p K halg inf_le_right]
  congr 1
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp]
  rfl

omit [∀ W : X.Opens, Algebra R Γ(X, W)] in
lemma fibre_cover (hcov : ⊤ ≤ iSup U) :
    (⊤ : (pullback p (fibreMap K)).Opens) ≤ ⨆ i, pullback.fst p (fibreMap K) ⁻¹ᵁ U i := by
  intro y _
  have : pullback.fst p (fibreMap K) y ∈ iSup U := hcov trivial
  simpa [Opens.mem_iSup] using this

set_option backward.isDefEq.respectTransparency false in
/-- The fibrewise Čech hypothesis: if global functions on the fibre `X_K` are constants, every
`K`-fibre Čech cocycle comes from `K`. -/
lemma fibre_hyp [Finite ι] (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⊤ ≤ iSup U)
    (hq : IsIso (pullback.snd p (fibreMap K)).appTop) (x : K ⊗[R] (∀ i, Γ(X, U i)))
    (hx : Algebra.TensorProduct.map (AlgHom.id R K) (cechLeft p halg U) x =
      Algebra.TensorProduct.map (AlgHom.id R K) (cechRight p halg U) x) :
    x ∈ Set.range (algebraMap K (K ⊗[R] (∀ i, Γ(X, U i)))) := by
  obtain ⟨s, hs, -⟩ := (pullback p (fibreMap K)).sheaf.existsUnique_gluing'
    (fun i ↦ pullback.fst p (fibreMap K) ⁻¹ᵁ U i) ⊤ (fun _ ↦ homOfLE le_top)
    (fibre_cover p U K hcov) (fun i ↦ fibreComp p halg U K i x) (by
      intro i j
      refine (fibreComp_cechLeft p halg U K x i j).trans ?_
      rw [hx]
      exact (fibreComp_cechRight p halg U K x i j).symm)
  obtain ⟨t, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp hq).2 s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom t, fibreComp_injective p halg U K hU ?_⟩
  refine funext fun i ↦ ?_
  dsimp only
  rw [fibreComp_algebraMap, ← hs i, fibreSec, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  rfl

omit [∀ W : X.Opens, Algebra R Γ(X, W)] in
lemma nontrivial_sections_top (hq : IsIso (pullback.snd p (fibreMap K)).appTop) :
    Nontrivial Γ(pullback p (fibreMap K), ⊤) :=
  ((asIso (pullback.snd p (fibreMap K)).appTop).symm ≪≫
    Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

include halg in
/-- The fibre of the Čech algebra over `K` is nonzero. -/
lemma fibre_nontrivial (hcov : ⊤ ≤ iSup U) (hq : IsIso (pullback.snd p (fibreMap K)).appTop) :
    Nontrivial (K ⊗[R] (∀ i, Γ(X, U i))) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := nontrivial_sections_top p K hq
  have h1 (i : ι) :
      (1 : Γ(pullback p (fibreMap K), pullback.fst p (fibreMap K) ⁻¹ᵁ U i)) = 0 := by
    rw [← map_one (fibreComp p halg U K i), ← map_zero (fibreComp p halg U K i),
      Subsingleton.elim (1 : K ⊗[R] (∀ i, Γ(X, U i))) 0]
  have h2 : (1 : Γ(pullback p (fibreMap K), ⊤)) = 0 :=
    (pullback p (fibreMap K)).sheaf.eq_of_locally_eq'
      (fun i ↦ pullback.fst p (fibreMap K) ⁻¹ᵁ U i) ⊤ (fun _ ↦ homOfLE le_top)
      (fibre_cover p U K hcov) _ _ fun i ↦ by
        change ((pullback p (fibreMap K)).presheaf.map (homOfLE le_top).op).hom 1 =
          ((pullback p (fibreMap K)).presheaf.map (homOfLE le_top).op).hom 0
        rw [map_one, map_zero]
        exact h1 i
  exact one_ne_zero h2

include halg in
set_option backward.isDefEq.respectTransparency false in
/-- Čech argument over an affine base: a finite affine cover with affine pairwise intersections,
constant global functions on all fibres and the Čech criterion give `IsIso p.appTop`. -/
theorem isIso_appTop_of_cover [Smooth p] [Finite ι] (hU : ∀ i, IsAffineOpen (U i))
    (hUU : ∀ i j, IsAffineOpen (U i ⊓ U j)) (hcov : ⊤ ≤ iSup U)
    (hfib : ∀ (P : Ideal R) [P.IsPrime],
      IsIso (pullback.snd p (fibreMap P.ResidueField)).appTop)
    (hC : Langlands.Algebra.SmoothEqualizerFibreCriterion.{u}) : IsIso p.appTop := by
  have (i : ι) : Algebra.Smooth R Γ(X, U i) :=
    RingHom.smooth_algebraMap.mp (by rw [halg]; exact smooth_secHom p (hU i))
  have (ij : ι × ι) : Algebra.Smooth R Γ(X, U ij.1 ⊓ U ij.2) :=
    RingHom.smooth_algebraMap.mp (by rw [halg]; exact smooth_secHom p (hUU ij.1 ij.2))
  have h₀ : Algebra.Smooth R (∀ i, Γ(X, U i)) := {}
  have h₁ : Algebra.Smooth R (∀ ij : ι × ι, Γ(X, U ij.1 ⊓ U ij.2)) := {}
  have hff : Module.FaithfullyFlat R (∀ i, Γ(X, U i)) :=
    Module.FaithfullyFlat.of_comap_surjective fun P ↦
      (P.nontrivial_iff_mem_rangeComap).mp (fibre_nontrivial p halg U _ hcov (hfib P.asIdeal))
  have key := hC R (∀ i, Γ(X, U i)) (∀ ij : ι × ι, Γ(X, U ij.1 ⊓ U ij.2)) (cechLeft p halg U)
    (cechRight p halg U) h₀ h₁ hff
    (fun P _ x hx ↦ fibre_hyp p halg U P.ResidueField hU hcov (hfib P) x hx)
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab ↦ ?_, fun s ↦ ?_⟩
  · apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    apply FaithfulSMul.algebraMap_injective R (∀ i, Γ(X, U i))
    funext i
    change algebraMap R Γ(X, U i) _ = algebraMap R Γ(X, U i) _
    rw [halg]
    change (secHom p (U i)).hom ((Scheme.ΓSpecIso R).hom a) =
      (secHom p (U i)).hom ((Scheme.ΓSpecIso R).hom b)
    rw [secHom_apply, secHom_apply, hab]
  · obtain ⟨r, hr⟩ := key (fun i ↦ (X.presheaf.map (homOfLE le_top).op).hom s) (by
      funext ij
      change (X.presheaf.map (homOfLE inf_le_left).op).hom
          ((X.presheaf.map (homOfLE le_top).op).hom s) =
        (X.presheaf.map (homOfLE inf_le_right).op).hom
          ((X.presheaf.map (homOfLE le_top).op).hom s)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl)
    refine ⟨(Scheme.ΓSpecIso R).inv r, X.sheaf.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top)
      hcov _ _ fun i ↦ ?_⟩
    have h2 : (secHom p (U i)).hom r = (X.presheaf.map (homOfLE le_top).op).hom s := by
      rw [← halg]
      exact congr_fun hr i
    refine (secHom_apply p (U i) _).symm.trans ?_
    rw [Iso.inv_hom_id_apply]
    exact h2

end Cech

/-- The case of an affine base `Spec R`, assuming the field case and the Čech criterion. -/
theorem isIso_appTop_of_spec (hF : FieldSmoothProperConnectedGlobalFunctions.{u})
    (hC : Langlands.Algebra.SmoothEqualizerFibreCriterion.{u}) {R : CommRingCat.{u}}
    {X : Scheme.{u}} (p : X ⟶ Spec R) [Smooth p] [IsProper p] [GeometricallyConnected p] :
    IsIso p.appTop := by
  let _ : ∀ W : X.Opens, Algebra R Γ(X, W) := fun W ↦ (secHom p W).hom.toAlgebra
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by simpa using isCompact_univ)
  have := hs.to_subtype
  refine isIso_appTop_of_cover p (fun _ ↦ rfl) (fun i : s ↦ i.1.1) (fun i ↦ i.1.2)
    (fun i j ↦ (isAffineHom_diagonal_iff (f := p)).mp inferInstance ⊤ (isAffineOpen_top _) _
      (by simp) _ (by simp) i.1.2 j.1.2) (by rw [iSup_subtype]; exact e.le) (fun P _ ↦ ?_) hC
  exact hF P.ResidueField _ (pullback.snd p (fibreMap P.ResidueField))
    inferInstance inferInstance inferInstance

/-- The main theorem, assuming the field case and the Čech criterion. -/
theorem main (hF : FieldSmoothProperConnectedGlobalFunctions.{u})
    (hC : Langlands.Algebra.SmoothEqualizerFibreCriterion.{u}) :
    SmoothProperConnectedGlobalFunctions.{u} := by
  intro X S p _ _ _ U
  refine isIso_app_of_forall_isAffineOpen p (fun V hV ↦ ?_) U
  have : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : GeometricallyConnected ((p ∣_ V) ≫ hV.isoSpec.hom) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected _ _).mpr inferInstance
  have h := isIso_appTop_of_spec hF hC ((p ∣_ V) ≫ hV.isoSpec.hom)
  rw [Scheme.Hom.comp_appTop] at h
  have : IsIso hV.isoSpec.hom.appTop := by
    rw [IsAffineOpen.isoSpec_hom_appTop]; infer_instance
  have h' : IsIso (p ∣_ V).appTop := IsIso.of_isIso_comp_left hV.isoSpec.hom.appTop _
  rw [morphismRestrict_appTop, eqToHom_op, eqToHom_map] at h'
  have h'' : IsIso (p.app (V.ι ''ᵁ ⊤)) := by
    generalize_proofs at h'
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
      (Iso.isIso_hom (eqToIso ‹(_ : CommRingCat) = _›)) h'
  rwa [Scheme.Opens.ι_image_top] at h''

end Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

namespace Langlands.AlgebraicGeometry

/-- For a smooth proper morphism with geometrically connected fibres, the canonical map
`p.app U` on sections is an isomorphism over every open `U` of the base. -/
theorem smoothProperConnectedGlobalFunctions : SmoothProperConnectedGlobalFunctions.{u} :=
  SmoothProperConnectedGlobalFunctionsProof.main fieldSmoothProperConnectedGlobalFunctions
    Langlands.Algebra.smoothEqualizerFibreCriterion

end Langlands.AlgebraicGeometry
