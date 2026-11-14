import Langlands.Geometry.Analytic.EtaleSite

/-!
# Underlying points of covering sieves in the analytic étale site

This module states the missing converse to the existing assertion that a
jointly surjective sieve is covering.
-/

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

universe u v

/-- Every covering sieve in the analytic étale site is jointly surjective on
underlying points. This is a statement, without a proof. -/
def EtaleCoveringPointsStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (X : LocalizedCategory.{u, v, v} (K := K)) ⦃U : EtaleSite X⦄ (S : Sieve U),
    S ∈ etaleTopology X U →
      ∀ x : (EtaleSite.points X).obj U,
        ∃ (V : EtaleSite X) (f : V ⟶ U), S f ∧
          x ∈ Set.range ((EtaleSite.points X).map f)

end Langlands.Analytic.SaturatedAtlasPresentation
