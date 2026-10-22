import Langlands.Cohomology.Continuous.CochainComparison

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- Discrete invertibility and general naturality of the canonical actual-cohomology comparison. -/
def CochainComparisonLaws : Prop :=
  (∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
    (A : TopRep.{u} k G),
    IsIso (continuousToOrdinaryCochains A) ∧
      (∀ n : ℕ, IsIso ((continuousToOrdinaryCochains A).f n)) ∧
      ∀ q : ℕ, IsIso (continuousToOrdinary A q)) ∧
  ∀ (k G H : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (A : TopRep.{u} k G) (B : TopRep.{u} k H)
    (φ : H →ₜ* G) (f : TopRep.res φ A ⟶ B),
    (((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap φ f) ≫
        continuousToOrdinaryCochains B =
      continuousToOrdinaryCochains A ≫
        groupCohomology.cochainsMap (φ : H →* G) (Rep.ofHom f.hom.toIntertwiningMap)) ∧
    ∀ q : ℕ,
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map φ f q) ≫ continuousToOrdinary B q =
        continuousToOrdinary A q ≫
          groupCohomology.map (φ : H →* G) (Rep.ofHom f.hom.toIntertwiningMap) q

end Langlands.Continuous
