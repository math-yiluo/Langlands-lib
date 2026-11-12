import Langlands.Representation.Hecke.NondegenerateModuleFunctor

/-! # Smooth representations and nondegenerate Hecke modules (Renard III.1.4, Theorem)

The published functor from smooth representations of a t.d. group `G` to nondegenerate
modules over its Haar Hecke algebra is an equivalence of categories.
-/

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Hecke

/-- Renard III.1.4, Theorem: for a t.d. group `G` (a Hausdorff, locally compact nonarchimedean
topological group, as in Renard II.1.1) with a left Haar measure `μ`, the published functor
`heckeNondegenerateModuleFunctor μ : M(G) ⥤ M(H(G))`, which sends a smooth representation to
its carrier with the integrated Hecke action, is an equivalence of categories, for carriers
in any universe `v`. -/
def HeckeNondegenerateModuleEquivalenceStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure],
    (heckeNondegenerateModuleFunctor.{u, v} μ).IsEquivalence

end Langlands.Hecke
