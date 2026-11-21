import Langlands.Representation.CompactCoefficient.CompactProjectionDistributionConstruction

/-! # A compact isotypic projector on a noncompact group is not a Hecke operator -/

noncomputable section

open MeasureTheory

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- On a noncompact, σ-compact locally profinite group with a bi-invariant Haar
measure, no single Hecke function induces the isotypic projector of an irreducible
compact representation on all smooth objects. -/
def CompactIsotypicProjectorNotHeckeStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (D : IrreducibleCompactCoefficientRep.{u, v} G), ¬ IsCompact (Set.univ : Set G) →
    ¬ ∃ e : Hecke.HeckeAlgebra μ,
      ∀ (A : SmoothRep.{0, u, v} ℂ G) (x : A),
        Hecke.heckeAction μ A.representation A.isSmooth e x =
          ProjectionDistribution.projector μ D A x

end Langlands.Renard.CompactRepresentation
