import Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement
import Langlands.AllField.Representation.Jacquet.Parabolic
/-! Supercuspidality of the factors of a quasicuspidal standard-Levi tensor.
This is a derived proposition target, not a proof of reflection. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviTensorSupercuspidalReflectionStatement
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uW

/-- Quasicuspidality of the actual block tensor forces supercuspidality of
each irreducible admissible smooth factor. -/
def PadicLeviTensorSupercuspidalReflectionStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ A : ∀ i : Fin B.length,
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F),
      (∀ i, (A i).IsIrreducible) →
      (∀ i, (A i).IsAdmissible) →
      IsLeviQuasicuspidal B (B.blockTensor (fun i => (A i).representation)) →
      ∀ i, GeneralLinear.IsSupercuspidal (A i).representation

end Langlands.AllField.CuspidalSupport
