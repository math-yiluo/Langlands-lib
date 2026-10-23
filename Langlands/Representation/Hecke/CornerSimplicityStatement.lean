import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.Category.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! Simplicity of nonzero fixed spaces over the actual compact-open Hecke corner. -/

namespace Langlands.Hecke

open MeasureTheory

universe uG uV

/-- The forward direction of Bernstein--Zelevinsky (1976), Proposition 2.10(a): for an
irreducible smooth complex representation `A` of a Hausdorff, locally compact, totally
disconnected group with a left Haar measure `μ`, and a compact open subgroup `K` with a
nonzero `K`-fixed space, that fixed space is a simple module over the corner
`HeckeAlgebra.Corner μ K hK` acting through `cornerModule`. -/
def CornerFixedVectorsSimplicityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (A : SmoothRep.{0, uG, uV} ℂ G),
    A.IsIrreducible →
    ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      fixedVectors A.representation K.toSubgroup ≠ ⊥ →
      letI := cornerModule μ A.representation A.isSmooth K hK
      IsSimpleModule (HeckeAlgebra.Corner μ K hK)
        (fixedVectors A.representation K.toSubgroup)

end Langlands.Hecke
