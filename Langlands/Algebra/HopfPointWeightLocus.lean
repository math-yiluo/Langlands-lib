import Langlands.Algebra.HopfPointWeightWindow
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # The weight-window locus: base change, field descent and openness -/

noncomputable section

open TensorProduct Coalgebra

namespace Langlands.Algebra.HopfPointWeightLocus

open HopfPointExtension HopfPointWeightWindow

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {M : Type*} [AddCommGroup M]
  {V : Type*} [AddCommGroup V] [Module R V] (δ : V →ₗ[R] V ⊗[R] A)
  {D : Type*} [CommRing D] [Algebra R D]

theorem proj_mapAlgHom_tmul (ψ : C →ₐ[R] D) (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M)
    (d : D) (v : V) :
    proj δ ((AddMonoidAlgebra.mapAlgHom M ψ).comp β) l (d ⊗ₜ v) =
      d • (ψ.toLinearMap.rTensor V) (proj δ β l (1 ⊗ₜ v)) := by
  have h1 : (d ⊗ₜ v : D ⊗[R] V) = d • ((1 : D) ⊗ₜ v) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : (ψ.toLinearMap.rTensor V) ((1 : C) ⊗ₜ v) = (1 : D) ⊗ₜ v := by
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  rw [h1, map_smul, rTensor_proj, h2]

/-- Weight windows are preserved by change of coefficients. -/
theorem weightsIn_mapAlgHom (ψ : C →ₐ[R] D) {β : A →ₐ[R] AddMonoidAlgebra C M} {T : Set M}
    (h : WeightsIn δ β T) : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom M ψ).comp β) T := by
  intro l hl x
  induction x with
  | tmul d v => rw [proj_mapAlgHom_tmul, h l hl, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- Weight windows descend along a change of coefficients injective on `· ⊗ V`. -/
theorem weightsIn_of_mapAlgHom (ψ : C →ₐ[R] D)
    (hinj : Function.Injective (ψ.toLinearMap.rTensor V)) {β : A →ₐ[R] AddMonoidAlgebra C M}
    {T : Set M} (h : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom M ψ).comp β) T) :
    WeightsIn δ β T := by
  intro l hl x
  apply hinj
  rw [rTensor_proj, h l hl, map_zero]

/-- Over a field, scalar extension to a nonzero algebra is injective on `· ⊗ V`. -/
theorem rTensor_injective_of_field {K : Type*} [Field K] [Algebra R K] {L : Type*} [CommRing L]
    [Nontrivial L] [Algebra R L] (ψ : K →ₐ[R] L) :
    Function.Injective (ψ.toLinearMap.rTensor V) := by
  let : Algebra K L := ψ.toRingHom.toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  have hff : Module.FaithfullyFlat K L := inferInstance
  have key : ψ.toLinearMap.rTensor V =
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L V).toLinearMap.restrictScalars R
        ∘ₗ (TensorProduct.mk K L (K ⊗[R] V) 1).restrictScalars R) := by
    apply TensorProduct.ext'
    intro k v
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, TensorProduct.mk_apply,
      LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [key, LinearMap.coe_comp]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L V).injective.comp
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) (K ⊗[R] V))

theorem rTensor_smul (ψ : C →ₐ[R] D) (g : C) (y : C ⊗[R] V) :
    (ψ.toLinearMap.rTensor V) (g • y) = ψ g • (ψ.toLinearMap.rTensor V) y := by
  induction y with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.smul_tmul', AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Openness of the weight window: if the weights at the residue field of `p` lie in `T`,
they lie in `T` after inverting some element outside `p`. -/
theorem exists_away_weightsIn [Module.Finite R V] (hδ : IsCoassoc δ)
    {β : A →ₐ[R] AddMonoidAlgebra C M} (hβ : IsHopfPoint β) (T : Set M) (p : Ideal C)
    [p.IsPrime]
    (hwin : WeightsIn δ ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp β) T) :
    ∃ f ∉ p, WeightsIn δ ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C (Localization.Away f))).comp β) T := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_finite_weightsIn δ β
  have hl : ∀ l : M, ∃ g ∉ p, l ∉ T → ∀ x, g • proj δ β l x = 0 := by
    intro l
    by_cases hlT : l ∈ T
    · exact ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
        fun h => absurd hlT h⟩
    · let K := p.ResidueField
      let e := proj δ β l
      have he : ∀ x, e (e x) = e x := proj_proj δ β l hδ hβ
      have hzero : e.lTensor K = 0 := by
        apply LinearMap.ext
        intro y
        apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R C K K V).injective
        rw [LinearMap.zero_apply, map_zero]
        induction y with
        | tmul k z =>
          rw [LinearMap.lTensor_tmul, cancelBaseChange_tmul_eq, rTensor_proj, hwin l hlT,
            smul_zero]
        | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
      obtain ⟨f, hfp, hf⟩ := exists_smul_eq_zero_of_idempotent e he p hzero
      exact ⟨f, hfp, fun _ => hf⟩
  choose g hgp hg using hl
  let f := ∏ l ∈ T₀, g l
  have hf : f ∉ p := by
    intro hmem
    obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hgp l hl
  refine ⟨f, hf, ?_⟩
  intro l hl x
  induction x with
  | tmul d v =>
    rw [proj_mapAlgHom_tmul]
    by_cases hl₀ : l ∈ T₀
    · have hunit : IsUnit (IsScalarTower.toAlgHom R C (Localization.Away f) (g l)) := by
        apply isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hl₀))
        exact IsLocalization.Away.algebraMap_isUnit f
      have h0 := congrArg (fun y : C ⊗[R] V =>
        ((IsScalarTower.toAlgHom R C (Localization.Away f)).toLinearMap.rTensor V) y)
        (hg l hl ((1 : C) ⊗ₜ v))
      rw [rTensor_smul, map_zero] at h0
      rw [(hunit.smul_eq_zero).mp h0, smul_zero]
    · rw [hT₀ l (by simpa using hl₀), map_zero, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

end Langlands.Algebra.HopfPointWeightLocus
