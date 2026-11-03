import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Invariant derivations of a polynomial bialgebra -/

noncomputable section

open TensorProduct MvPolynomial Matrix

namespace Langlands.Algebra.GradedHopf

section Counit

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A]

/-- The counit identity `∑ ε(a₂) • a₁ = a` for any representation of `comul a`. -/
theorem sum_counit_right_smul_left {ι : Type*} {a : A} (ℛ : Coalgebra.Repr k a ι) :
    ∑ i ∈ ℛ.index, Coalgebra.counit (R := k) (ℛ.right i) • ℛ.left i = a := by
  have h := congrArg (TensorProduct.rid k A) (Coalgebra.sum_tmul_counit_eq ℛ)
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using h

end Counit

section Coordinates

variable {k A σ : Type*} [CommRing k] [CommRing A] [Bialgebra k A]
  {z : σ → A} (hz : Function.Bijective (MvPolynomial.aeval z : MvPolynomial σ k →ₐ[k] A))

/-- The coordinate isomorphism `MvPolynomial σ k ≃ₐ[k] A` given by `z`. -/
abbrev coordEquiv : MvPolynomial σ k ≃ₐ[k] A := AlgEquiv.ofBijective _ hz

/-- The partial derivative `∂/∂zᵢ` on `A`, transported from `MvPolynomial.pderiv i`. -/
def coordDeriv (i : σ) : Derivation k A A where
  toLinearMap := (coordEquiv hz).toLinearMap ∘ₗ (pderiv i).toLinearMap ∘ₗ
    (coordEquiv hz).symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change coordEquiv hz (pderiv i ((coordEquiv hz).symm (a * b))) =
      a • coordEquiv hz (pderiv i ((coordEquiv hz).symm b)) +
        b • coordEquiv hz (pderiv i ((coordEquiv hz).symm a))
    rw [map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul]

theorem coordDeriv_apply (i : σ) (a : A) :
    coordDeriv hz i a = coordEquiv hz (pderiv i ((coordEquiv hz).symm a)) :=
  rfl

theorem coordEquiv_X (i : σ) : coordEquiv hz (X i) = z i := by
  simp

variable [DecidableEq σ]

theorem coordDeriv_z (i j : σ) : coordDeriv hz i (z j) = if j = i then 1 else 0 := by
  rw [coordDeriv_apply, ← coordEquiv_X hz j, AlgEquiv.symm_apply_apply, pderiv_X]
  by_cases h : j = i
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, map_zero]
    simp [h]

omit [DecidableEq σ] in
include hz in
theorem adjoin_range_eq_top : Algebra.adjoin k (Set.range z) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
  exact hz.2

omit [Bialgebra k A] [DecidableEq σ] in
theorem derivation_sum_apply {ι : Type*} [Algebra k A] (t : Finset ι)
    (f : ι → Derivation k A A) (a : A) : (∑ i ∈ t, f i) a = ∑ i ∈ t, f i a := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx ih => rw [Finset.sum_insert hx, Derivation.add_apply, ih, Finset.sum_insert hx]

/-- The chain rule: a derivation of `A` is determined by its values on the coordinates. -/
theorem derivation_eq_sum [Fintype σ] (D : Derivation k A A) (a : A) :
    D a = ∑ j, D (z j) * coordDeriv hz j a := by
  let D' : Derivation k A A := ∑ j, D (z j) • coordDeriv hz j
  have h : D = D' := by
    refine Derivation.ext_of_adjoin_eq_top (Set.range z) (adjoin_range_eq_top hz) ?_
    rintro _ ⟨i, rfl⟩
    simp [D', coordDeriv_z]
  conv_lhs => rw [h]
  simp only [D', derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- The tangent vector `ε ∘ ∂/∂zᵢ` at the counit. -/
def coordTangent (i : σ) : A →ₗ[k] k :=
  Coalgebra.counit ∘ₗ (coordDeriv hz i).toLinearMap

omit [DecidableEq σ] in
theorem coordTangent_apply (i : σ) (a : A) :
    coordTangent hz i a = Coalgebra.counit (R := k) (coordDeriv hz i a) :=
  rfl

omit [DecidableEq σ] in
theorem coordTangent_mul (i : σ) (a b : A) :
    coordTangent hz i (a * b) = Coalgebra.counit (R := k) a * coordTangent hz i b +
      Coalgebra.counit (R := k) b * coordTangent hz i a := by
  simp only [coordTangent_apply, Derivation.leibniz, smul_eq_mul, map_add,
    Bialgebra.counit_mul]

omit [DecidableEq σ] in
theorem coordTangent_one (i : σ) : coordTangent hz i 1 = 0 := by
  simp [coordTangent_apply]

theorem coordTangent_z (i j : σ) : coordTangent hz i (z j) = if j = i then 1 else 0 := by
  rw [coordTangent_apply, coordDeriv_z]
  split_ifs <;> simp

omit [DecidableEq σ] in
theorem coordTangent_eq_zero_of_mem_sq (i : σ) {x : A}
    (hx : x ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) : coordTangent hz i x = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · have ha' : Coalgebra.counit (R := k) a = 0 := ha
    have hb' : Coalgebra.counit (R := k) b = 0 := hb
    rw [coordTangent_mul, ha', hb']
    simp
  · rw [map_add, hx, hy, add_zero]

/-- The left-invariant derivation `a ↦ ∑ a₁ ξᵢ(a₂)` attached to the tangent vector
`ξᵢ = coordTangent hz i`. -/
def invariantDerivLinear (i : σ) : A →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A (coordTangent hz i) ∘ₗ
    Coalgebra.comul

omit [DecidableEq σ] in
theorem invariantDerivLinear_repr (i : σ) {ι : Type*} {a : A} (ℛ : Coalgebra.Repr k a ι) :
    invariantDerivLinear hz i a = ∑ j ∈ ℛ.index, coordTangent hz i (ℛ.right j) • ℛ.left j := by
  simp only [invariantDerivLinear, LinearMap.coe_comp, Function.comp_apply, ← ℛ.eq, map_sum,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

omit [DecidableEq σ] in
theorem invariantDerivLinear_mul (i : σ) (a b : A) :
    invariantDerivLinear hz i (a * b) =
      a * invariantDerivLinear hz i b + b * invariantDerivLinear hz i a := by
  classical
  let ℛa := Coalgebra.Repr.arbitrary k a
  let ℛb := Coalgebra.Repr.arbitrary k b
  have hab : Coalgebra.comul (R := k) (a * b) =
      ∑ x ∈ ℛa.index, ∑ y ∈ ℛb.index,
        (ℛa.left x * ℛb.left y) ⊗ₜ[k] (ℛa.right x * ℛb.right y) := by
    rw [Bialgebra.comul_mul, ← ℛa.eq, ← ℛb.eq, Finset.sum_mul_sum]
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
  have hl : invariantDerivLinear hz i (a * b) = ∑ x ∈ ℛa.index, ∑ y ∈ ℛb.index,
      coordTangent hz i (ℛa.right x * ℛb.right y) • (ℛa.left x * ℛb.left y) := by
    simp only [invariantDerivLinear, LinearMap.coe_comp, Function.comp_apply, hab, map_sum,
      LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  calc invariantDerivLinear hz i (a * b)
      = ∑ x ∈ ℛa.index, ∑ y ∈ ℛb.index,
          coordTangent hz i (ℛa.right x * ℛb.right y) • (ℛa.left x * ℛb.left y) := hl
    _ = (∑ x ∈ ℛa.index, Coalgebra.counit (R := k) (ℛa.right x) • ℛa.left x) *
          (∑ y ∈ ℛb.index, coordTangent hz i (ℛb.right y) • ℛb.left y) +
        (∑ y ∈ ℛb.index, Coalgebra.counit (R := k) (ℛb.right y) • ℛb.left y) *
          (∑ x ∈ ℛa.index, coordTangent hz i (ℛa.right x) • ℛa.left x) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := ℛb.index),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [coordTangent_mul]
      simp only [Algebra.smul_def, map_add, map_mul]
      ring
    _ = a * invariantDerivLinear hz i b + b * invariantDerivLinear hz i a := by
      rw [sum_counit_right_smul_left ℛa, sum_counit_right_smul_left ℛb,
        invariantDerivLinear_repr hz i ℛa, invariantDerivLinear_repr hz i ℛb]

/-- The left-invariant derivation attached to `coordTangent hz i`. -/
def invariantDeriv (i : σ) : Derivation k A A where
  toLinearMap := invariantDerivLinear hz i
  map_one_eq_zero' := by
    simp [invariantDerivLinear, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      coordTangent_one]
  leibniz' a b := by
    simp only [smul_eq_mul]
    exact invariantDerivLinear_mul hz i a b

theorem invariantDeriv_apply (i : σ) (a : A) :
    invariantDeriv hz i a = invariantDerivLinear hz i a :=
  rfl

theorem counit_invariantDeriv (i : σ) (a : A) :
    Coalgebra.counit (R := k) (invariantDeriv hz i a) = coordTangent hz i a := by
  let ℛ := Coalgebra.Repr.arbitrary k a
  rw [invariantDeriv_apply, invariantDerivLinear_repr hz i ℛ, map_sum]
  conv_rhs => rw [← Coalgebra.sum_counit_smul ℛ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

theorem invariantDeriv_of_isPrimitiveElem (i : σ) {f : A} (hf : Bialgebra.IsPrimitiveElem k f) :
    invariantDeriv hz i f = algebraMap k A (coordTangent hz i f) := by
  rw [invariantDeriv_apply, invariantDerivLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    hf.comul_eq_tmul_add_tmul]
  simp [coordTangent_one, Algebra.smul_def]

/-- A primitive element in the square of the augmentation ideal of a domain with polynomial
coordinates `z` has all partial derivatives `∂/∂zⱼ` equal to zero. -/
theorem coordDeriv_eq_zero_of_mem_sq [Fintype σ] [IsDomain A] {f : A}
    (hf : Bialgebra.IsPrimitiveElem k f)
    (hf2 : f ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) (j : σ) :
    coordDeriv hz j f = 0 := by
  have hδ : ∀ i, invariantDeriv hz i f = 0 := fun i => by
    rw [invariantDeriv_of_isPrimitiveElem hz i hf, coordTangent_eq_zero_of_mem_sq hz i hf2,
      map_zero]
  let N : Matrix σ σ A := fun i j => invariantDeriv hz i (z j)
  let v : σ → A := fun j => coordDeriv hz j f
  have hNv : N *ᵥ v = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, N, v, Pi.zero_apply]
    rw [← derivation_eq_sum hz, hδ]
  have hmap : (Bialgebra.counitAlgHom k A : A →+* k).mapMatrix N = 1 := by
    ext i j
    change Coalgebra.counit (R := k) (invariantDeriv hz i (z j)) = (1 : Matrix σ σ k) i j
    rw [counit_invariantDeriv, coordTangent_z, Matrix.one_apply]
    simp [eq_comm]
  have hdet : (Bialgebra.counitAlgHom k A : A →+* k) N.det = 1 := by
    rw [RingHom.map_det, hmap, Matrix.det_one]
  have hdet0 : N.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    have h1 : (1 : A) = 0 := by
      rw [← map_one (algebraMap k A), ← hdet, map_zero]
    exact one_ne_zero h1
  have hsmul : N.det • v = 0 := by
    have h := congrArg (fun u => N.adjugate *ᵥ u) hNv
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h
    exact h
  have := congrFun hsmul j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left hdet0

/-- The same statement for the polynomial representing `f`. -/
theorem pderiv_eq_zero_of_mem_sq [Fintype σ] [IsDomain A] {f : A}
    (hf : Bialgebra.IsPrimitiveElem k f)
    (hf2 : f ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) (j : σ) :
    pderiv j ((coordEquiv hz).symm f) = 0 := by
  have := coordDeriv_eq_zero_of_mem_sq hz hf hf2 j
  rw [coordDeriv_apply] at this
  exact (coordEquiv hz).injective (by rw [this, map_zero])

end Coordinates

end Langlands.Algebra.GradedHopf
