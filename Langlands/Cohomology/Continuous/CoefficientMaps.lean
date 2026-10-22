import Langlands.Cohomology.Continuous.FiniteQuotientComparison

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- The actual fixed-coefficient map induces a map of the finite cochain systems. -/
noncomputable def finiteCochainCoefficient {A B : Rep.{u} k G} (f : A ⟶ B) :
    finiteQuotientCochainDiagram A ⟶ finiteQuotientCochainDiagram B where
  app N := groupCohomology.cochainsMap (MonoidHom.id _)
    ((Rep.quotientToInvariantsFunctor k (OrderDual.ofDual N).toSubgroup).map f)
  naturality N M h := by
    change groupCohomology.cochainsMap
        (quotientTransition (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
          (leOfHom (X := FiniteQuotientIndex (G := G)) h))
        (fixedTransition A (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
          (leOfHom (X := FiniteQuotientIndex (G := G)) h)) ≫
        groupCohomology.cochainsMap (MonoidHom.id _)
          ((Rep.quotientToInvariantsFunctor k (OrderDual.ofDual M).toSubgroup).map f) =
      groupCohomology.cochainsMap (MonoidHom.id _)
          ((Rep.quotientToInvariantsFunctor k (OrderDual.ofDual N).toSubgroup).map f) ≫
        groupCohomology.cochainsMap
          (quotientTransition (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
            (leOfHom (X := FiniteQuotientIndex (G := G)) h))
          (fixedTransition B (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
            (leOfHom (X := FiniteQuotientIndex (G := G)) h))
    rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
    apply groupCohomology.cochainsMap_congr
    · ext x
      rfl
    · rfl

/-- The induced coefficient map between actual finite cohomology diagrams. -/
noncomputable def finiteCohomologyCoefficient {A B : Rep.{u} k G} (f : A ⟶ B) (q : ℕ) :
    finiteQuotientDiagram A q ⟶ finiteQuotientDiagram B q :=
  Functor.whiskerRight (finiteCochainCoefficient f)
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q)

/-- Coefficient functoriality on the actual directed colimit. -/
noncomputable def finiteQuotientCoefficient {A B : Rep.{u} k G} (f : A ⟶ B) (q : ℕ) :
    finiteQuotientCohomology A q ⟶ finiteQuotientCohomology B q :=
  Limits.colimMap (finiteCohomologyCoefficient f q)

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] [IsTopologicalGroup G] in
theorem finiteCochainCoefficient_id (A : Rep.{u} k G) :
    finiteCochainCoefficient (𝟙 A) = 𝟙 (finiteQuotientCochainDiagram A) := by
  apply NatTrans.ext
  funext N
  change groupCohomology.cochainsMap
    (A := finiteQuotientRep A (OrderDual.ofDual N))
    (B := finiteQuotientRep A (OrderDual.ofDual N)) (MonoidHom.id _)
    ((Rep.quotientToInvariantsFunctor k (OrderDual.ofDual N).toSubgroup).map (𝟙 A)) = _
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] [IsTopologicalGroup G] in
theorem finiteCochainCoefficient_comp {A B C : Rep.{u} k G} (f : A ⟶ B) (g : B ⟶ C) :
    finiteCochainCoefficient (f ≫ g) = finiteCochainCoefficient f ≫ finiteCochainCoefficient g := by
  apply NatTrans.ext
  funext N
  change groupCohomology.cochainsMap
    (A := finiteQuotientRep A (OrderDual.ofDual N))
    (B := finiteQuotientRep C (OrderDual.ofDual N)) (MonoidHom.id _)
    ((Rep.quotientToInvariantsFunctor k (OrderDual.ofDual N).toSubgroup).map (f ≫ g)) = _
  rw [Functor.map_comp, groupCohomology.cochainsMap_id_comp]
  rfl

omit [TopologicalSpace k] [IsTopologicalGroup G] in
theorem finiteQuotientCoefficient_id (A : Rep.{u} k G) (q : ℕ) :
    finiteQuotientCoefficient (𝟙 A) q = 𝟙 (finiteQuotientCohomology A q) := by
  unfold finiteQuotientCoefficient finiteCohomologyCoefficient
  rw [finiteCochainCoefficient_id, Functor.whiskerRight_id']
  exact Limits.colim.map_id (finiteQuotientDiagram A q)

omit [TopologicalSpace k] [IsTopologicalGroup G] in
theorem finiteQuotientCoefficient_comp {A B C : Rep.{u} k G}
    (f : A ⟶ B) (g : B ⟶ C) (q : ℕ) :
    finiteQuotientCoefficient (f ≫ g) q =
      finiteQuotientCoefficient f q ≫ finiteQuotientCoefficient g q := by
  unfold finiteQuotientCoefficient finiteCohomologyCoefficient
  rw [finiteCochainCoefficient_comp, Functor.whiskerRight_comp]
  exact Limits.colim.map_comp _ _

/-- The actual continuous coefficient cochain map, with topology forgotten. -/
noncomputable def continuousCoefficientCochains {A B : DiscreteModule k G}
    (f : A.toTopRep ⟶ B.toTopRep) :
    underlyingContinuousCochains A.toTopRep ⟶ underlyingContinuousCochains B.toTopRep :=
  ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f)

end Langlands.Continuous
