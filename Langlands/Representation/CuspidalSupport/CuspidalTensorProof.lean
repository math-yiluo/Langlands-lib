import Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Tensor.FiniteProperties

/-!
# External tensors of supercuspidal block factors

The external tensor product of supercuspidal factors on the blocks of a
standard Levi is irreducible, admissible, and has zero coinvariants for every
proper standard refinement of the Levi.
-/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric PadicField.TopologicalData

universe uV uF

/-- The conjugate of a unipotent radical by the identity is the radical itself. -/
theorem conjugateUnipotent_one {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
    (B : BlockShape n) : B.conjugateUnipotent (F := F) 1 = B.unipotentSubgroup F := by
  ext x
  simp [BlockShape.conjugateUnipotent]

/-- A proper standard refinement of a product Levi is proper in some block. -/
theorem exists_parabolic_ne_top {F : Type uF} [Field F] {n : ℕ} {B : BlockShape n}
    (S : BlockRefinement B) (hS : refinedParabolic F B S ≠ ⊤) :
    ∃ i, (S i).parabolic F ≠ ⊤ := by
  by_contra h
  push Not at h
  apply hS
  rw [refinedParabolic, funext h, Subgroup.pi_top]

/-- Proof of `GLCuspidalTensorStatement`. -/
theorem glCuspidalTensor : GLCuspidalTensorStatement.{uV, uF} := by
  intro p _ F T n _
  let := T.topology
  intro B A
  have hirr : ∀ i, (A i).obj.representation.IsIrreducible := fun i => (A i).property.1
  have hsc : ∀ i, IsSupercuspidal (A i).obj.representation := fun i => (A i).property.2
  refine ⟨?_, ?_, ?_⟩
  · exact FiniteTensor.isIrreducible_external (fun i => (A i).obj.representation)
      (fun i φ => (admissibleSchur_scalarEndomorphism _ (hsc i).1 (hirr i) φ).exists)
  · exact FiniteTensor.isAdmissible_external _ (fun i => (hsc i).1)
  · intro S hS
    obtain ⟨j, hj⟩ := exists_parabolic_ne_top S hS
    have hj' := (hsc j).2 (S j) hj 1
    rw [conjugateUnipotent_one] at hj'
    exact FiniteTensor.coinvariants_external_subsingleton _ _ j hj'

end Langlands.CuspidalSupport
