import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement
import Langlands.AllField.Group.GL.BlockModulus
/-! Small-carrier tensor exhaustion for irreducible cuspidal standard Levis.
This is a derived theorem target, not a proof of factorization or shrinking. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviCuspidalFactorizationStatement
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uW uV

/-- Every irreducible cuspidal representation of an actual standard local-field
Levi is equivalent to the external tensor of irreducible supercuspidal block
representations, whose carriers lie in an independently prescribed universe. -/
def PadicLeviCuspidalFactorizationStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uW} ℂ (B.Levi F),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      ∃ A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, uV} (F := F) (n := B.size i),
        Nonempty (σ.representation.Equiv
          (B.blockTensor (fun i => (A i).obj.representation)))

end Langlands.AllField.CuspidalSupport
