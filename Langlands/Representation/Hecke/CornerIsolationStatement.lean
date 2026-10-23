import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.CompactCoefficient.Classes

/-! # Actual Hecke corner elements isolating a compact-coefficient irreducible -/

namespace Langlands.Hecke

open MeasureTheory

universe uG uV uW

/-- The existence clause of BZ76 Theorem 2.42(a), restricted to `K`-fixed vectors:
some element of the published test-function corner acts by `cornerAction` as the
identity on the fixed vectors of the chosen irreducible representation with compact
smooth-dual coefficients, and as zero on the fixed vectors of every inequivalent
irreducible smooth representation. -/
def CompactCoefficientCornerIsolationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant]
    (A : SmoothRep.{0, uG, uV} ℂ G),
    A.IsIrreducible →
    HasCompactSmoothDualCoefficients A.representation →
    ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      ∃ e : HeckeAlgebra.Corner μ K hK,
        cornerAction μ A.representation A.isSmooth K hK e = 1 ∧
        ∀ (B : SmoothRep.{0, uG, uW} ℂ G),
          B.IsIrreducible →
          ¬ Nonempty (A.representation.Equiv B.representation) →
          cornerAction μ B.representation B.isSmooth K hK e = 0

end Langlands.Hecke
