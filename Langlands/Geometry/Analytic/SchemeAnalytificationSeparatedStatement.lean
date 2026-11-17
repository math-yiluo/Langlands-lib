import Langlands.Geometry.Analytic.SchemeAnalytificationGluingStatement

/-! # Statement: separatedness and Hausdorff scheme analytification -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology

/-- The separatedness criterion of Berkovich 1990, Theorem 3.4.8(i), for the
Library's glued polynomial-locus analytification. This is exactly the fifth
clause of `SchemeAnalytificationGluingStatement`. -/
def SchemeAnalytificationSeparatedStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f],
    IsSeparated f ↔ T2Space (Space K f)

theorem separatedStatement_of_gluingStatement
    (h : SchemeAnalytificationGluingStatement.{u}) :
    SchemeAnalytificationSeparatedStatement.{u} := by
  intro K _ _ _ X f _
  exact (h K X f).2.2.2.2

end Langlands.Analytic.SchemeAnalytification
