import Langlands.Cohomology.Continuous.CoefficientMaps

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- The finite quotient comparison respects the actual continuous coefficient morphisms. -/
def CoefficientComparisonLaws : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A B : DiscreteModule k G) (f : A.toTopRep ⟶ B.toTopRep),
    (∀ N : OpenNormalSubgroup G,
      (finiteCochainCoefficient (Rep.ofHom f.hom.toIntertwiningMap)).app
          (OrderDual.toDual N) ≫ finiteStageCochainMap B N =
        finiteStageCochainMap A N ≫ continuousCoefficientCochains f) ∧
    (∀ (N : OpenNormalSubgroup G) (q : ℕ),
      (finiteCohomologyCoefficient (Rep.ofHom f.hom.toIntertwiningMap) q).app
          (OrderDual.toDual N) ≫ finiteStageToContinuous B N q =
        finiteStageToContinuous A N q ≫
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
            (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q)) ∧
    ∀ q : ℕ,
      finiteQuotientCoefficient (Rep.ofHom f.hom.toIntertwiningMap) q ≫
          finiteQuotientComparison B q =
        finiteQuotientComparison A q ≫
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
            (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q)

end Langlands.Continuous
