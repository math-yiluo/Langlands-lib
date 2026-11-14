import Langlands.CategoryTheory.Sites.PointwiseCovering
import Langlands.Geometry.Analytic.EtaleSite

/-! # Pointwise lifting squares in the analytic étale site -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

/-- Compatible ordinary points of any cospan in the analytic étale site
lift through an actual étale object and a commuting square.
This is a statement, without a proof. -/
def EtalePointwiseLiftingStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (X : LocalizedCategory.{u, v, v} (K := K)) ⦃U V W : EtaleSite X⦄
    (f : U ⟶ W) (g : V ⟶ W) (x : (EtaleSite.points X).obj U)
    (y : (EtaleSite.points X).obj V),
    (EtaleSite.points X).map f x = (EtaleSite.points X).map g y →
      ∃ (T : EtaleSite X) (p : T ⟶ U) (q : T ⟶ V),
        p ≫ f = q ≫ g ∧
          ∃ t : (EtaleSite.points X).obj T,
            (EtaleSite.points X).map p t = x ∧ (EtaleSite.points X).map q t = y

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The geometric statement is precisely the pointwise-square hypothesis
of the generic covering-points criterion, for every analytic base. -/
theorem etalePointwiseLiftingStatement_iff :
    EtalePointwiseLiftingStatement.{u, v} K ↔
      ∀ X : LocalizedCategory.{u, v, v} (K := K),
        Langlands.CategoryTheory.PointwiseCovering.HasPointwiseLiftingSquares
          (EtaleSite.points X) :=
  Iff.rfl

/-- The pointwise-lifting statement implies that every étale covering sieve
is jointly surjective on ordinary underlying points. -/
theorem jointlySurjective_of_mem_etaleTopology_of_pointwiseLifting
    (h : EtalePointwiseLiftingStatement.{u, v} K)
    {X : LocalizedCategory.{u, v, v} (K := K)} {U : EtaleSite X} (S : Sieve U)
    (hS : S ∈ etaleTopology X U) :
    ∀ x : (EtaleSite.points X).obj U,
      ∃ (V : EtaleSite X) (f : V ⟶ U), S f ∧
        x ∈ Set.range ((EtaleSite.points X).map f) :=
  Langlands.CategoryTheory.PointwiseCovering.isJointlySurjective_of_mem_toGrothendieck
    (h X) hS

end Langlands.Analytic.SaturatedAtlasPresentation
