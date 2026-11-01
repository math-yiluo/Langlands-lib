import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Smooth.IrreducibleRealization

/-!
# Irreducible images up to sign under the actual Aubert operator

This is the GL specialization of preservation of irreducibility up to sign in
Aubert Corollary 3.9(a,b), with the corrected complex proof recorded in the
companion Markdown. It states a proposition and supplies no proof of it.
-/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The existing unadjusted Aubert operator sends the exact class of every
actual irreducible smooth GL representation to an actual irreducible class
or its negative. Both finite-length witnesses follow from irreducibility. -/
def IrreducibleImageStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : Representation.IsIrreducible π.representation),
    ∃ (πD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπD : Representation.IsIrreducible πD.representation),
      let x := GeneralLinear.finiteLengthClass n F.Carrier π
        (SmoothRep.hasFiniteLength_of_isIrreducible hπ)
      let y := GeneralLinear.finiteLengthClass n F.Carrier πD
        (SmoothRep.hasFiniteLength_of_isIrreducible hπD)
      alternatingOperator.{uF, uV} F T n x = y ∨
        alternatingOperator.{uF, uV} F T n x = -y

end Langlands.Aubert
