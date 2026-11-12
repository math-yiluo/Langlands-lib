import Langlands.Sheaf.Renard.SheafProjectorComparison

/-!
# Statements: Renard's II.2.5 Theorem on compact sections

Renard (9 July 2026), II.2.5 Theorem and its proof, printed pp.39–40 / PDF pp.45–46.
-/

namespace Langlands.Sheaf.Renard.CompactSectionEquivalence

open CategoryTheory

/-- The original-sheaf comparison `F ⟶ P(Γc F)` is an isomorphism for every complex
vector sheaf on a t.d. space. -/
def SheafComparisonIsIso : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)
    (F : VectorSheafScalars.VectorSheaf X),
    IsIso (SheafProjectorComparison.sheafComparison F hX)

/-- The compact-section functor to nondegenerate test modules is an equivalence. -/
def CompactSectionFunctorIsEquivalence : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X),
    (CompactSectionTestModule.compactSectionFunctor hX).IsEquivalence

/-- The projector sheaf functor from nondegenerate test modules is an equivalence. -/
def ProjectorFunctorIsEquivalence : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X),
    (ProjectorVectorSheaf.functor.{0, 0} hX).IsEquivalence

end Langlands.Sheaf.Renard.CompactSectionEquivalence
