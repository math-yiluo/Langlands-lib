import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement
/-!
# External tensors of supercuspidal block factors

The external tensor product of supercuspidal factors on the blocks of a
standard Levi is irreducible, admissible, and has zero coinvariants for every
proper standard refinement of the Levi.
-/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding GLCuspidalTensorStatement glCuspidalTensor
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric
open Langlands.LocalFieldData

universe uV uF

/-- Proof of `GLCuspidalTensorStatement`. -/
theorem glCuspidalTensor : GLCuspidalTensorStatement.{uV, uF} := by
  intro F _ T n _
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

end Langlands.AllField.CuspidalSupport
