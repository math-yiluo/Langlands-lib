import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeDensity
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Rational density in the fixed ground-field torus envelope

The published finite Galois splitting theorem discharges the sole input of
the existing density bridge. It also supplies an actual rational point
meeting every nonempty open of any representative of the fixed envelope.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Every representative of the fixed torus envelope has dense rational
points over an infinite field, with no structural proposition as input. -/
theorem torusGeneratedEnvelopeRationalDensity :
    TorusGeneratedEnvelopeRationalDensityStatement.{u} :=
  torusGeneratedEnvelopeRationalDensity_of_finiteGaloisSplitting
    torusFiniteGaloisSplitting

variable {k : Type u} [Field k] [Infinite k]

/-- Select an actual rational point meeting a supplied nonempty open of the
fixed torus envelope. Ambient connectedness is unnecessary. -/
def TorusGeneratedEnvelope.rationalPointMeetingOpen
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (D : TorusGeneratedEnvelope G)
    (U : D.group.X.left.Opens) (hU : (U : Set D.group.X.left).Nonempty) :
    {p : RationalPoint k D.group.X // ∃ x, p.left x ∈ U} :=
  D.rationalPointMeetingOpenOfFiniteGaloisSplitting
    torusFiniteGaloisSplitting U hU

end Langlands.GroupScheme
