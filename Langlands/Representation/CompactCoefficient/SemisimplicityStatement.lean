import Langlands.Representation.CompactCoefficient.Classes
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.RepresentationTheory.Semisimple

/-!
# Semisimplicity of smooth representations with compact coefficients

This is a proposition, not a proof. It states the final sentence of
Bernstein--Zelevinsky (1976), Theorem 2.44(b), with the hypotheses of
Section 2.42 retained.
-/

namespace Langlands

open MeasureTheory

universe uG uV

/-- Every smooth complex representation with compact smooth-dual matrix
coefficients is semisimple: its lattice of subrepresentations is complemented.
The representation is arbitrary otherwise. A regular two-sided Haar measure
makes the unimodularity hypothesis explicit. -/
def CompactCoefficientSemisimplicityStatement
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
    [Measure.IsMulRightInvariant μ] : Prop :=
  ∀ A : SmoothRep.{0, uG, uV} ℂ G,
    HasCompactSmoothDualCoefficients A.representation →
    Representation.IsSemisimpleRepresentation A.representation

end Langlands
