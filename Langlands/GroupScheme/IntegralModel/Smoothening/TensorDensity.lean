import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Detecting divisibility on tensor products by product functionals

A family of linear forms on a vector space *detects zero* if the only vector killed
by every form is zero. Families detecting zero on two vector spaces give, by
tensor products, a family detecting zero on their tensor product.

Over a local ring `R`, a family of `R`-valued linear forms on a module `C`
*detects the maximal ideal* if every element whose values all lie in the maximal
ideal lies in `𝔪 C`. This property is stable under tensor products, and over a
discrete valuation ring it implies divisibility of elements by every nonzero `s`
dividing all their values. -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening

section Field

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A family of linear forms detects zero if only zero is killed by all of them. -/
def Detects {ι : Type*} (F : ι → V →ₗ[k] k) : Prop :=
  ∀ v : V, (∀ i, F i v = 0) → v = 0

/-- Families detecting zero on `V` and `W` detect zero on `V ⊗ W` through the
products of their forms. -/
theorem detects_tensor {ι κ : Type*} {F : ι → V →ₗ[k] k} {G : κ → W →ₗ[k] k}
    (hF : Detects F) (hG : Detects G) (x : V ⊗[k] W)
    (hx : ∀ i j, TensorProduct.lid k k (TensorProduct.map (F i) (G j) x) = 0) : x = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext l
  rw [Finsupp.zero_apply]
  apply hG
  intro j
  have hv : TensorProduct.rid k V ((G j).lTensor V x) = 0 := by
    apply hF
    intro i
    have h1 : F i ∘ₗ (TensorProduct.rid k V).toLinearMap ∘ₗ (G j).lTensor V =
        (TensorProduct.lid k k).toLinearMap ∘ₗ TensorProduct.map (F i) (G j) :=
      TensorProduct.ext' fun v w => by simp [mul_comm]
    have := LinearMap.congr_fun h1 x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, hx i j]
  have h2 : G j ∘ₗ (TensorProduct.lid k W).toLinearMap ∘ₗ (b.coord l).rTensor W =
      b.coord l ∘ₗ (TensorProduct.rid k V).toLinearMap ∘ₗ (G j).lTensor V :=
    TensorProduct.ext' fun v w => by simp [mul_comm]
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
  have := LinearMap.congr_fun h2 x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
  rw [this, hv, map_zero]

end Field

section Local

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {C D : Type*} [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

theorem one_tmul_eq_zero_iff (c : C) :
    (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ∈ (maximalIdeal R) • (⊤ : Submodule R C) := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := C) (maximalIdeal R) c,
    LinearEquiv.map_eq_zero_iff]
  rfl

theorem exists_one_tmul_eq (z : ResidueField R ⊗[R] C) :
    ∃ c : C, (1 : ResidueField R) ⊗ₜ[R] c = z := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.quotTensorEquivQuotSMul C (maximalIdeal R) z)
  refine ⟨c, ?_⟩
  have h := (TensorProduct.quotTensorEquivQuotSMul C (maximalIdeal R)).symm_apply_apply z
  rw [← hc, TensorProduct.quotTensorEquivQuotSMul_symm_mk] at h
  exact h

/-- The reduction of an `R`-valued linear form to the residue field. -/
def reduceForm (f : C →ₗ[R] R) : ResidueField R ⊗[R] C →ₗ[ResidueField R] ResidueField R :=
  (TensorProduct.AlgebraTensorModule.rid R (ResidueField R) (ResidueField R)).toLinearMap ∘ₗ
    f.baseChange (ResidueField R)

@[simp]
theorem reduceForm_one_tmul (f : C →ₗ[R] R) (c : C) :
    reduceForm f ((1 : ResidueField R) ⊗ₜ c) = residue R (f c) := by
  simp [reduceForm, Algebra.smul_def]

/-- A family of `R`-valued forms detects the maximal ideal if each element all of
whose values lie in the maximal ideal lies in `𝔪 C`. -/
def DetectsMaximal {ι : Type*} (F : ι → C →ₗ[R] R) : Prop :=
  ∀ c : C, (∀ i, F i c ∈ maximalIdeal R) → c ∈ (maximalIdeal R) • (⊤ : Submodule R C)

theorem DetectsMaximal.detects {ι : Type*} {F : ι → C →ₗ[R] R} (hF : DetectsMaximal F) :
    Detects (fun i => reduceForm (F i)) := by
  intro z hz
  obtain ⟨c, rfl⟩ := exists_one_tmul_eq z
  rw [one_tmul_eq_zero_iff]
  refine hF c fun i => ?_
  have := hz i
  simp only [reduceForm_one_tmul] at this
  exact (residue_eq_zero_iff _).1 this

/-- The product forms on a tensor product. -/
def productForm (f : C →ₗ[R] R) (g : D →ₗ[R] R) : C ⊗[R] D →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map f g

omit [IsLocalRing R] in
@[simp]
theorem productForm_tmul (f : C →ₗ[R] R) (g : D →ₗ[R] R) (c : C) (d : D) :
    productForm f g (c ⊗ₜ d) = f c * g d := by
  simp [productForm]

theorem residue_productForm (f : C →ₗ[R] R) (g : D →ₗ[R] R) (x : C ⊗[R] D) :
    TensorProduct.lid _ _ (TensorProduct.map (reduceForm f) (reduceForm g)
        (TensorProduct.AlgebraTensorModule.distribBaseChange R (ResidueField R) C D
          ((1 : ResidueField R) ⊗ₜ x))) =
      residue R (productForm f g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c d =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
    simp
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add,
      map_add]

/-- Detection of the maximal ideal is stable under tensor products. -/
theorem DetectsMaximal.tensor {ι κ : Type*} {F : ι → C →ₗ[R] R} {G : κ → D →ₗ[R] R}
    (hF : DetectsMaximal F) (hG : DetectsMaximal G) :
    DetectsMaximal (fun p : ι × κ => productForm (F p.1) (G p.2)) := by
  intro x hx
  rw [← one_tmul_eq_zero_iff]
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R (ResidueField R) C D).injective
  rw [map_zero]
  refine detects_tensor hF.detects hG.detects _ fun i j => ?_
  rw [residue_productForm]
  exact (residue_eq_zero_iff _).2 (hx (i, j))

end Local

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {C : Type*} [AddCommGroup C] [Module R C]

/-- Over a discrete valuation ring, detection of the maximal ideal gives divisibility
by every nonzero element dividing all values. -/
theorem DetectsMaximal.exists_eq_smul {ι : Type*} {F : ι → C →ₗ[R] R}
    (hF : DetectsMaximal F) {s : R} (hs : s ≠ 0) (c : C) (hc : ∀ i, s ∣ F i c) :
    ∃ c' : C, c = s • c' := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  clear hs
  induction n generalizing c with
  | zero =>
    refine ⟨(↑u⁻¹ : R) • c, ?_⟩
    rw [pow_zero, mul_one, smul_smul, Units.mul_inv, one_smul]
  | succ n ih =>
    have hmem : c ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C) := by
      refine hF c fun i => ?_
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
      exact (Dvd.intro_left _ (by ring : (↑u * ϖ ^ n) * ϖ = ↑u * ϖ ^ (n + 1))).trans (hc i)
    rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨c₁, -, rfl⟩ := hmem
    have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
    obtain ⟨c₂, rfl⟩ := ih c₁ fun i => by
      have h := hc i
      rw [map_smul, smul_eq_mul, pow_succ, ← mul_assoc, mul_comm _ ϖ] at h
      exact (mul_dvd_mul_iff_left hϖ0).1 h
    refine ⟨c₂, ?_⟩
    rw [smul_smul, pow_succ]
    congr 1
    ring

end DVR

end Langlands.GroupScheme.IntegralModel.Smoothening
