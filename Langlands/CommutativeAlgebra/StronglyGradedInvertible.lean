import Langlands.CommutativeAlgebra.StronglyGraded
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Invertibility of the components of a strongly graded ring -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.StronglyGraded

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M]
variable {c : A →+* AddMonoidAlgebra A M}

/-- The product of homogeneous elements of opposite degrees has degree zero. -/
theorem mul_mem_degreeZero {m : M} {a b : A}
    (ha : a ∈ component (c := c) m) (hb : b ∈ component (c := c) (-m)) :
    a * b ∈ degreeZero (c := c) := by
  have h := mul_mem_component ha hb
  rw [add_neg_cancel] at h
  exact h

/-- The product of homogeneous elements of opposite degrees, in the other order. -/
theorem mul_mem_degreeZero' {m : M} {a b : A}
    (ha : a ∈ component (c := c) (-m)) (hb : b ∈ component (c := c) m) :
    a * b ∈ degreeZero (c := c) := by
  have h := mul_mem_component ha hb
  rw [neg_add_cancel] at h
  exact h

/-- Multiplication pairs the components of degrees `m` and `-m` into degree zero. -/
def mulPairing (m : M) :
    component (c := c) m →ₗ[degreeZero (c := c)]
      component (c := c) (-m) →ₗ[degreeZero (c := c)] degreeZero (c := c) :=
  LinearMap.mk₂ (degreeZero (c := c))
    (fun a b => ⟨(a : A) * b, mul_mem_degreeZero a.property b.property⟩)
    (fun a a' b => Subtype.ext (add_mul (a : A) a' b))
    (fun r a b => Subtype.ext (by
      change ((r : A) * a) * b = (r : A) * (a * b)
      ring))
    (fun a b b' => Subtype.ext (mul_add (a : A) b b'))
    (fun r a b => Subtype.ext (by
      change (a : A) * ((r : A) * b) = (r : A) * (a * b)
      ring))

@[simp] theorem mulPairing_apply (m : M) (a : component (c := c) m)
    (b : component (c := c) (-m)) :
    ((mulPairing m a b : degreeZero (c := c)) : A) = (a : A) * b := rfl

/-- The multiplication map from the tensor product of opposite components. -/
def mulTensor (m : M) :
    component (c := c) m ⊗[degreeZero (c := c)] component (c := c) (-m) →ₗ[degreeZero (c := c)]
      degreeZero (c := c) :=
  TensorProduct.lift (mulPairing m)

@[simp] theorem mulTensor_tmul (m : M) (a : component (c := c) m)
    (b : component (c := c) (-m)) :
    ((mulTensor m (a ⊗ₜ b) : degreeZero (c := c)) : A) = (a : A) * b := rfl

section DualFamily

variable {m : M} (n : ℕ) (x y : Fin n → A)
  (hx : ∀ i, x i ∈ component (c := c) (-m)) (hy : ∀ i, y i ∈ component (c := c) m)

/-- The tensor obtained from a dual family of degree `-m`, with the degree `m` factor first. -/
def dualTensor : component (c := c) m ⊗[degreeZero (c := c)] component (c := c) (-m) :=
  ∑ i, (⟨y i, hy i⟩ : component (c := c) m) ⊗ₜ (⟨x i, hx i⟩ : component (c := c) (-m))

include hx hy in
/-- A pure tensor is its product times the dual tensor. -/
theorem tmul_eq_smul_dualTensor (hsum : ∑ i, x i * y i = 1)
    (a : component (c := c) m) (b : component (c := c) (-m)) :
    a ⊗ₜ[degreeZero (c := c)] b = mulTensor m (a ⊗ₜ b) • dualTensor n x y hx hy := by
  classical
  -- Expand `a` along the partition of unity.
  have ha : a = ∑ i, (⟨(a : A) * x i, mul_mem_degreeZero a.property (hx i)⟩ :
      degreeZero (c := c)) • (⟨y i, hy i⟩ : component (c := c) m) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def, algebraMap_degreeZero]
    calc (a : A) = (a : A) * ∑ i, x i * y i := by rw [hsum, mul_one]
      _ = ∑ i, (a : A) * x i * y i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  conv_lhs => rw [ha]
  rw [TensorProduct.sum_tmul, dualTensor, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul, Algebra.smul_def, algebraMap_degreeZero, mulTensor_tmul]
  ring

include hx hy in
/-- Every tensor is its multiplication image times the dual tensor. -/
theorem eq_smul_dualTensor (hsum : ∑ i, x i * y i = 1)
    (t : component (c := c) m ⊗[degreeZero (c := c)] component (c := c) (-m)) :
    t = mulTensor m t • dualTensor n x y hx hy := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact tmul_eq_smul_dualTensor n x y hx hy hsum a b
  | add t t' ht ht' => rw [map_add, add_smul, ← ht, ← ht']

include hx hy in
/-- The multiplication image of the dual tensor is one. -/
theorem mulTensor_dualTensor (hsum : ∑ i, x i * y i = 1) :
    mulTensor m (dualTensor n x y hx hy) = 1 := by
  apply Subtype.ext
  simp only [dualTensor, map_sum, AddSubmonoidClass.coe_finsetSum, mulTensor_tmul, OneMemClass.coe_one]
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end DualFamily

/-- In a strongly graded ring, multiplication identifies the tensor product of the
components of degrees `m` and `-m` with the degree-zero ring. -/
theorem mulTensor_bijective {m : M} (hs : HasDualFamily (c := c) (-m)) :
    Function.Bijective (mulTensor (c := c) m) := by
  obtain ⟨n, x, y, hx, hy, hsum⟩ := hs
  have hy' : ∀ i, y i ∈ component (c := c) m := fun i => by
    simpa only [neg_neg] using hy i
  constructor
  · intro t t' h
    rw [eq_smul_dualTensor n x y hx hy' hsum t, eq_smul_dualTensor n x y hx hy' hsum t', h]
  · intro r
    refine ⟨r • dualTensor n x y hx hy', ?_⟩
    rw [map_smul, mulTensor_dualTensor n x y hx hy' hsum, smul_eq_mul, mul_one]

/-- The multiplication isomorphism of a strong grading in degree `m`. -/
def mulTensorEquiv {m : M} (hs : HasDualFamily (c := c) (-m)) :
    component (c := c) m ⊗[degreeZero (c := c)] component (c := c) (-m) ≃ₗ[degreeZero (c := c)]
      degreeZero (c := c) :=
  LinearEquiv.ofBijective _ (mulTensor_bijective hs)

/-- Each component of a strongly graded commutative ring is an invertible module over
the degree-zero ring. -/
theorem invertible_component {m : M} (hs : HasDualFamily (c := c) (-m)) :
    Module.Invertible (degreeZero (c := c)) (component (c := c) m) :=
  Module.Invertible.left (mulTensorEquiv hs)

/-- Each component of a strongly graded ring has rank one at every prime of the
degree-zero ring. -/
theorem rankAtStalk_component {m : M} (hs : HasDualFamily (c := c) (-m))
    (p : PrimeSpectrum (degreeZero (c := c))) :
    Module.rankAtStalk (component (c := c) m) p = 1 := by
  have := invertible_component hs
  exact Module.Invertible.finrank_eq_one _ _

/-- If a component is free of rank one, its generator is a unit of the graded ring. -/
theorem isUnit_of_linearEquiv {m : M} (hs : HasDualFamily (c := c) (-m))
    (e : component (c := c) m ≃ₗ[degreeZero (c := c)] degreeZero (c := c)) :
    IsUnit ((e.symm 1 : component (c := c) m) : A) := by
  obtain ⟨n, x, y, hx, hy, hsum⟩ := hs
  have hy' : ∀ i, y i ∈ component (c := c) m := fun i => by
    simpa only [neg_neg] using hy i
  have hgen : ∀ i, y i = (e ⟨y i, hy' i⟩ : A) * (e.symm 1 : A) := by
    intro i
    have h : (⟨y i, hy' i⟩ : component (c := c) m) = e ⟨y i, hy' i⟩ • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    exact congrArg Subtype.val h
  refine IsUnit.of_mul_eq_one (∑ i, x i * (e ⟨y i, hy' i⟩ : A)) ?_
  rw [Finset.mul_sum, ← hsum]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [hgen i]
  ring

end Langlands.CommutativeAlgebra.StronglyGraded
