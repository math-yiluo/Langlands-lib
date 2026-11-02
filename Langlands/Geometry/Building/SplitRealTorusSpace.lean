import Langlands.Geometry.Building.RealTorusSpace

/-! # Real coordinates of the actual split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

variable (k : Type u) [Field k] (I : Type u) [Finite I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I

/-- Real cocharacter coordinates induced by the actual split-torus lattice equivalence. -/
def splitCocharacterCoordinates : V 𝕋 ≃ₗ[ℝ] (I → ℝ) :=
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  (LinearEquiv.baseChange ℤ ℝ _ _ (splitTorus.cocharacterLatticeEquiv k I).toIntLinearEquiv).trans
    (TensorProduct.piScalarRight ℤ ℝ ℝ I)

/-- Real character coordinates induced by the actual split-torus lattice equivalence. -/
def splitCharacterCoordinates : Vstar 𝕋 ≃ₗ[ℝ] (I → ℝ) :=
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  (LinearEquiv.baseChange ℤ ℝ _ _ (splitTorus.characterLatticeEquiv k I).toIntLinearEquiv).trans
    (TensorProduct.piScalarRight ℤ ℝ ℝ I)

@[simp] theorem splitCocharacterCoordinates_tmul (r : ℝ) (ν : cocharacterLattice 𝕋) :
    splitCocharacterCoordinates k I (r ⊗ₜ[ℤ] ν) =
      fun j => r * (splitTorus.cocharacterLatticeEquiv k I ν j : ℝ) := by
  ext j
  simp [splitCocharacterCoordinates, TensorProduct.piScalarRight_apply, zsmul_eq_mul, mul_comm]

@[simp] theorem splitCharacterCoordinates_tmul (r : ℝ) (χ : characterLattice 𝕋) :
    splitCharacterCoordinates k I (r ⊗ₜ[ℤ] χ) =
      fun j => r * (splitTorus.characterLatticeEquiv k I χ j : ℝ) := by
  ext j
  simp [splitCharacterCoordinates, TensorProduct.piScalarRight_apply, zsmul_eq_mul, mul_comm]

/-- An empty split torus has the zero cocharacter translation space. -/
theorem eq_zero_of_isEmpty_cocharacter [IsEmpty I] (v : V 𝕋) : v = 0 := by
  apply (splitCocharacterCoordinates k I).injective
  exact Subsingleton.elim _ _

/-- An empty split torus has the zero real character space. -/
theorem eq_zero_of_isEmpty_character [IsEmpty I] (x : Vstar 𝕋) : x = 0 := by
  apply (splitCharacterCoordinates k I).injective
  exact Subsingleton.elim _ _

/-- Both coordinate maps remain actual equivalences onto the empty function space. -/
theorem splitCocharacterCoordinates_eq_zero_of_isEmpty [IsEmpty I] (v : V 𝕋) :
    splitCocharacterCoordinates k I v = 0 := Subsingleton.elim _ _

theorem splitCharacterCoordinates_eq_zero_of_isEmpty [IsEmpty I] (x : Vstar 𝕋) :
    splitCharacterCoordinates k I x = 0 := Subsingleton.elim _ _

variable [Fintype I]

/-- In split-torus real coordinates the extended pairing is the finite dot product. -/
theorem pair_eq_sum (x : Vstar 𝕋) (v : V 𝕋) :
    pair 𝕋 x v = ∑ j, splitCharacterCoordinates k I x j * splitCocharacterCoordinates k I v j := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    induction v using TensorProduct.inductionOn with
    | tmul s ν =>
      simp only [pair_tmul_tmul, splitCharacterCoordinates_tmul, splitCocharacterCoordinates_tmul]
      rw [splitTorus.latticePairing_eq_sum]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    | add v w hv hw =>
      simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hv, hw]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, hx, hy]

/-- The empty-coordinate dot product is zero, including its actual tensor inputs. -/
theorem pair_eq_zero_of_isEmpty [IsEmpty I] (x : Vstar 𝕋) (v : V 𝕋) :
    pair 𝕋 x v = 0 := by
  rw [pair_eq_sum]
  exact Finset.sum_eq_zero fun j _ => isEmptyElim j

end Langlands.GroupScheme.RealTorusSpace
