import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The isometry group of a bilinear form; the standard symplectic form

For a bilinear form `B` on a module `W` over a commutative ring `R`,
`LinearMap.BilinForm.isometryGroup B` is the subgroup of the `R`-linear automorphisms `g` of `W`
with `B (g x) (g y) = B x y`. For an alternating non-degenerate form over a field this is the
symplectic group `Sp(W)` of GKT chapter 2 (p. 47).

`stdSymplecticForm l R` is the standard symplectic form on `l ⊕ l → R`,
`ω(w, w') = ∑ᵢ (w (inl i) w' (inr i) - w (inr i) w' (inl i)) = -(w ⬝ᵥ J *ᵥ w')`, and
`Matrix.symplecticGroup.toIsometryGroup l R` identifies Mathlib's group of symplectic matrices
(`A J Aᵀ = J`) with its isometry group, a matrix acting by `w ↦ A *ᵥ w`.
-/

namespace Langlands

namespace LinearMap.BilinForm

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/-- The group of `R`-linear automorphisms `g` of `W` preserving a bilinear form:
`B (g x) (g y) = B x y`. For an alternating non-degenerate form on a vector space this is the
symplectic group `Sp(W)` (GKT, chapter 2, p. 47). -/
def isometryGroup (B : LinearMap.BilinForm R W) : Subgroup (W ≃ₗ[R] W) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' {g h} hg hh x y := by
    change B (g (h x)) (g (h y)) = B x y
    rw [hg, hh]
  one_mem' x y := rfl
  inv_mem' {g} hg x y := by
    rw [← hg (g⁻¹ x) (g⁻¹ y)]
    change B (g (g.symm x)) (g (g.symm y)) = B x y
    simp

variable {B : LinearMap.BilinForm R W}

/-- Membership in the isometry group. -/
theorem mem_isometryGroup_iff {g : W ≃ₗ[R] W} :
    g ∈ isometryGroup B ↔ ∀ x y, B (g x) (g y) = B x y :=
  Iff.rfl

/-- An element of the isometry group preserves the form. -/
@[simp] theorem isometryGroup_apply (g : isometryGroup B) (x y : W) :
    B ((g : W ≃ₗ[R] W) x) ((g : W ≃ₗ[R] W) y) = B x y :=
  g.2 x y

/-- The product in the isometry group is composition. -/
@[simp] theorem coe_mul_apply (g h : isometryGroup B) (x : W) :
    ((g * h : isometryGroup B) : W ≃ₗ[R] W) x = (g : W ≃ₗ[R] W) ((h : W ≃ₗ[R] W) x) :=
  rfl

/-- The unit of the isometry group is the identity. -/
@[simp] theorem coe_one_apply (x : W) : ((1 : isometryGroup B) : W ≃ₗ[R] W) x = x :=
  rfl

end LinearMap.BilinForm

open Langlands.LinearMap.BilinForm (isometryGroup mem_isometryGroup_iff)

section StdSymplecticForm

open Matrix

variable (l : Type*) [Fintype l] (R : Type*) [CommRing R]

/-- The standard symplectic form on `l ⊕ l → R`:
`ω(w, w') = ∑ᵢ (w (inl i) w' (inr i) - w (inr i) w' (inl i)) = -(w ⬝ᵥ J *ᵥ w')`
(`stdSymplecticForm_apply`), preserved by `Matrix.symplecticGroup l R`. -/
def stdSymplecticForm : LinearMap.BilinForm R (l ⊕ l → R) :=
  LinearMap.mk₂ R
    (fun w w' => ∑ i, (w (Sum.inl i) * w' (Sum.inr i) - w (Sum.inr i) * w' (Sum.inl i)))
    (fun _ _ _ => by simp only [Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
    (fun _ _ _ => by simp only [Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)

variable {l R}

/-- The standard symplectic form in coordinates. -/
theorem stdSymplecticForm_apply_eq_sum (w w' : l ⊕ l → R) :
    stdSymplecticForm l R w w' =
      ∑ i, (w (Sum.inl i) * w' (Sum.inr i) - w (Sum.inr i) * w' (Sum.inl i)) := rfl

variable [DecidableEq l]

/-- The standard symplectic form through Mathlib's `Matrix.J`: `ω(w, w') = -(w ⬝ᵥ J *ᵥ w')`. -/
theorem stdSymplecticForm_apply (w w' : l ⊕ l → R) :
    stdSymplecticForm l R w w' = -(w ⬝ᵥ Matrix.J l R *ᵥ w') := by
  rw [stdSymplecticForm_apply_eq_sum]
  simp only [Matrix.J, dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    zero_add, add_zero, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_neg,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]; ring

/-- `ω(A w, A w') = w ⬝ᵥ (Aᵀ (-J) A) *ᵥ w'` for any matrix `A`. -/
private theorem stdSymplecticForm_mulVec_mulVec (A : Matrix (l ⊕ l) (l ⊕ l) R)
    (w w' : l ⊕ l → R) :
    stdSymplecticForm l R (A *ᵥ w) (A *ᵥ w') = -(w ⬝ᵥ (Aᵀ * Matrix.J l R * A) *ᵥ w') := by
  rw [stdSymplecticForm_apply]
  congr 1
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← dotProduct_mulVec]
  simp only [Matrix.mul_assoc]

/-- Symplectic matrices preserve the standard symplectic form. -/
theorem stdSymplecticForm_mulVec (g : Matrix.symplecticGroup l R) (w w' : l ⊕ l → R) :
    stdSymplecticForm l R (g.1 *ᵥ w) (g.1 *ᵥ w') = stdSymplecticForm l R w w' := by
  have hg : g.1ᵀ * Matrix.J l R * g.1 = Matrix.J l R := by
    have := SymplecticGroup.transpose_mem g.2
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at this
    exact this
  rw [stdSymplecticForm_mulVec_mulVec, hg, stdSymplecticForm_apply]

/-- A matrix whose action preserves the standard symplectic form is symplectic. -/
theorem mem_symplecticGroup_of_stdSymplecticForm {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : ∀ w w', stdSymplecticForm l R (A *ᵥ w) (A *ᵥ w') = stdSymplecticForm l R w w') :
    A ∈ Matrix.symplecticGroup l R := by
  have key : Aᵀ * Matrix.J l R * A = Matrix.J l R := by
    ext i j
    have h := hA (Pi.single i 1) (Pi.single j 1)
    rw [stdSymplecticForm_mulVec_mulVec, stdSymplecticForm_apply, neg_inj] at h
    simpa [mulVec_single, dotProduct_single] using h
  have hT : Aᵀ ∈ Matrix.symplecticGroup l R := by
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose]; exact key
  simpa using SymplecticGroup.transpose_mem hT

namespace Matrix.symplecticGroup

/-- The linear automorphism `w ↦ A *ᵥ w` of a symplectic matrix `A`. -/
def toLinearEquiv (g : _root_.Matrix.symplecticGroup l R) : (l ⊕ l → R) ≃ₗ[R] (l ⊕ l → R) where
  toFun w := g.1 *ᵥ w
  invFun w := (g⁻¹).1 *ᵥ w
  map_add' w w' := mulVec_add _ _ _
  map_smul' c w := mulVec_smul _ _ _
  left_inv w := by
    simp only [mulVec_mulVec]
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, one_mulVec]
  right_inv w := by
    simp only [mulVec_mulVec]
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one, one_mulVec]

variable (l R) in
/-- The action of symplectic matrices on `l ⊕ l → R`, as a homomorphism to the isometry group of
the standard symplectic form. -/
def toIsometryGroupHom :
    _root_.Matrix.symplecticGroup l R →* isometryGroup (stdSymplecticForm l R) where
  toFun g := ⟨toLinearEquiv g, stdSymplecticForm_mulVec g⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun w => one_mulVec w
  map_mul' g h := Subtype.ext <| LinearEquiv.ext fun w => (mulVec_mulVec w g.1 h.1).symm

theorem toIsometryGroupHom_bijective :
    Function.Bijective (toIsometryGroupHom l R) := by
  refine ⟨fun g h hgh => Subtype.ext ?_, fun e => ?_⟩
  · ext i j
    have := congrArg (fun e : isometryGroup (stdSymplecticForm l R) =>
      e.1 (Pi.single j 1) i) hgh
    simpa [toIsometryGroupHom, toLinearEquiv, mulVec_single] using this
  · set A := LinearMap.toMatrix' e.1.toLinearMap
    have hA : ∀ w, A *ᵥ w = e.1 w := fun w => LinearMap.toMatrix'_mulVec _ w
    refine ⟨⟨A, mem_symplecticGroup_of_stdSymplecticForm fun w w' => ?_⟩, ?_⟩
    · rw [hA, hA]; exact e.2 w w'
    · exact Subtype.ext <| LinearEquiv.ext fun w => hA w

variable (l R) in
/-- Mathlib's group of symplectic matrices is the isometry group of the standard symplectic form,
a matrix `A` acting by `w ↦ A *ᵥ w`. -/
noncomputable def toIsometryGroup :
    _root_.Matrix.symplecticGroup l R ≃* isometryGroup (stdSymplecticForm l R) :=
  MulEquiv.ofBijective (toIsometryGroupHom l R) toIsometryGroupHom_bijective

/-- A symplectic matrix acts on `l ⊕ l → R` by `w ↦ A *ᵥ w`. -/
@[simp] theorem toIsometryGroup_apply (g : _root_.Matrix.symplecticGroup l R) (w : l ⊕ l → R) :
    (toIsometryGroup l R g).1 w = g.1 *ᵥ w :=
  rfl

end Matrix.symplecticGroup

end StdSymplecticForm

end Langlands
