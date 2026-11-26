import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparisonFunctor
import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Geometric compact-support étale cohomological dimension

The absolute case of Berkovich 1993, Corollary 5.3.8, for bounded torsion
coefficients and a net of strictly affinoid charts. Harris uses this bound
in Fact 2 of his §2 to truncate the equivariant resolutions.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology

universe u v uL

/-- The ranges of the charts modelled by strictly affinoid algebras of Krull
dimension at most `d` form a net of the analytic space. -/
def HasStrictAffinoidDimensionBound
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K)) (d : ℕ) : Prop :=
  let atlas := (presentationOf X).presentation.atlas
  AtlasTopology.IsNet {V | ∃ i : atlas.Index, V = Set.range (atlas.chart i) ∧
    ∃ P : PresentedStrictAffinoidAlgebra K, Ring.KrullDimLE d P ∧
      Nonempty (atlas.algebra i ≅ PresentedAffinoidAlgebra.ofStrict K P)}

/-- On a Hausdorff analytic space with a strict affinoid dimension bound `d`
over an algebraically closed field, `H^q_c` of a bounded torsion module
sheaf vanishes for `q > 2 * d`. -/
def AnalyticEtaleCompactDimensionStatement
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    (d : ℕ) : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
    HasStrictAffinoidDimensionBound X d →
    ∀ N : ℕ, 0 < N →
      ∀ (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL}
          (ULift.{max u (v + 1) uL} (ZMod N)))) (q : ℕ),
        2 * d < q → IsZero ((etaleCompactCohomology L h (ULift (ZMod N)) q).obj F)

end Langlands.Cohomology
