import Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.AllField.Representation.Induction.BlockFactors
/-! Tensor-factor interfaces for the multiset form of cuspidal support. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding GLCuspidalTensorStatement
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.LocalFieldData

universe uV uF

/-- The external tensor product of irreducible supercuspidal block factors
is irreducible and cuspidal on the actual product Levi. -/
def GLCuspidalTensorStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ), 0 < n →
    letI := T.topology
    ∀ (B : BlockShape n)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F) (n := B.size i)),
      let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
      σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation

end Langlands.AllField.CuspidalSupport
