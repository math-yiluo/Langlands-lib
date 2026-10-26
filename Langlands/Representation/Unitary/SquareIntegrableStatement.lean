import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Unitarizability from square-integrable coefficients on a central quotient

This derived proposition exposes compact-open cofinality and right invariance
of the quotient Haar measure. It states the form-existence implication on the
original algebraic carrier and supplies no proof.
-/

namespace Langlands

universe uG uV

/-- An irreducible representation with square-integrable coefficients modulo the
center is unitarizable when compact open subgroups are cofinal and the specified
quotient Haar measure is right invariant. -/
def SquareIntegrableUnimodularUnitarityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V)
      [MeasurableSpace (G ⧸ Subgroup.center G)]
      [BorelSpace (G ⧸ Subgroup.center G)]
      (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
      [MeasureTheory.Measure.IsHaarMeasure μ]
      [MeasureTheory.Measure.IsMulRightInvariant μ],
      Representation.IsIrreducible ρ →
        IsSquareIntegrableModCenter ρ μ → IsUnitarizable ρ

end Langlands
