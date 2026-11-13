import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement
import Langlands.AllField.Group.GL.BlockModulus
/-! Same-universe finite tensor factorization of admissible irreducible
representations of actual standard local-field Levis. This is a derived theorem
target, not a proof of factorization. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviAdmissibleFactorizationStatement
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uW

/-- Every admissible irreducible representation of an actual standard local-field
Levi is equivalent to the external tensor of admissible irreducible block
representations whose carriers lie in the universe of the given carrier. -/
def PadicLeviAdmissibleFactorizationStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uW} ℂ (B.Levi F),
      σ.IsIrreducible → σ.IsAdmissible →
      ∃ A : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F),
        (∀ i, (A i).IsIrreducible) ∧ (∀ i, (A i).IsAdmissible) ∧
        Nonempty (σ.representation.Equiv
          (B.blockTensor (fun i => (A i).representation)))

end Langlands.AllField.CuspidalSupport
