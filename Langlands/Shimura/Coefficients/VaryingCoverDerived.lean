import Langlands.Shimura.Coefficients.VaryingCoverExact
import Langlands.Cohomology.ExactDerivedHomology

/-! # Derived association for varying finite geometric covers -/

noncomputable section

universe u uJ vJ wC wS wE

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))
variable [HasDerivedCategory.{wC} (EquivariantDiagram D (ModuleCat.{u} R))]
variable [HasDerivedCategory.{wS} (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))]

attribute [local instance] etaleAssociatedVaryingSystemFunctorPreservesFiniteLimits
  etaleAssociatedVaryingSystemFunctorPreservesFiniteColimits

/-- Actual association on the unbounded derived categories of varying-group
coefficient diagrams and associated small-etale sheaf diagrams. -/
def etaleAssociatedVaryingDerivedFunctor :
    DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R)) ⥤
      DerivedCategory (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  (etaleAssociatedVaryingSystemFunctor X Y hY).mapDerivedCategory

instance : (etaleAssociatedVaryingDerivedFunctor (R := R) X Y hY).CommShift ℤ := by
  dsimp [etaleAssociatedVaryingDerivedFunctor]
  infer_instance

instance : (etaleAssociatedVaryingDerivedFunctor (R := R) X Y hY).IsTriangulated := by
  dsimp [etaleAssociatedVaryingDerivedFunctor]
  infer_instance

/-- The derived functor is represented by the actual associated cochain complex. -/
def etaleAssociatedVaryingDerivedFactors :
    DerivedCategory.Q ⋙ etaleAssociatedVaryingDerivedFunctor (R := R) X Y hY ≅
      etaleAssociatedVaryingComplexFunctor X Y hY (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (etaleAssociatedVaryingSystemFunctor X Y hY).mapDerivedCategoryFactors

/-- The representative comparison uses the actual induced coefficient chain maps. -/
@[reassoc]
theorem etaleAssociatedVaryingDerivedFactors_naturality
    {K L : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ} (f : K ⟶ L) :
    (etaleAssociatedVaryingDerivedFunctor X Y hY).map (DerivedCategory.Q.map f) ≫
        (etaleAssociatedVaryingDerivedFactors X Y hY).hom.app L =
      (etaleAssociatedVaryingDerivedFactors X Y hY).hom.app K ≫
        DerivedCategory.Q.map
          ((etaleAssociatedVaryingComplexFunctor X Y hY (ComplexShape.up ℤ)).map f) :=
  (etaleAssociatedVaryingDerivedFactors X Y hY).hom.naturality f

/-- Association of a single-degree derived object is its associated sheaf diagram
placed in the same degree. -/
def etaleAssociatedVaryingDerivedSingleIso (q : ℤ) :
    DerivedCategory.singleFunctor (EquivariantDiagram D (ModuleCat.{u} R)) q ⋙
        etaleAssociatedVaryingDerivedFunctor X Y hY ≅
      etaleAssociatedVaryingSystemFunctor X Y hY ⋙
        DerivedCategory.singleFunctor
          (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q :=
  (etaleAssociatedVaryingSystemFunctor X Y hY).mapDerivedCategorySingleFunctor q

/-- Homology of a derived associated diagram is associated coefficient homology. -/
def etaleAssociatedVaryingDerivedHomologyIso (q : ℤ) :
    etaleAssociatedVaryingDerivedFunctor (R := R) X Y hY ⋙
        DerivedCategory.homologyFunctor
          (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q ≅
      DerivedCategory.homologyFunctor (EquivariantDiagram D (ModuleCat.{u} R)) q ⋙
        etaleAssociatedVaryingSystemFunctor X Y hY :=
  Langlands.Cohomology.exactDerivedHomologyIso
    (etaleAssociatedVaryingSystemFunctor X Y hY) q

/-- On a cochain representative, the derived comparison is precisely the
published association-homology comparison conjugated by localization. -/
@[reassoc]
theorem etaleAssociatedVaryingDerivedHomologyIso_hom_app_Q_obj (q : ℤ)
    (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ) :
    (etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app
        (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor
        (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q).map
          ((etaleAssociatedVaryingDerivedFactors X Y hY).hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors
          (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q).hom.app
            ((etaleAssociatedVaryingComplexFunctor X Y hY (ComplexShape.up ℤ)).obj K) ≫
        (etaleAssociatedVaryingHomologyIso X Y hY (ComplexShape.up ℤ) q).hom.app K ≫
        (etaleAssociatedVaryingSystemFunctor X Y hY).map
          ((DerivedCategory.homologyFunctorFactors
            (EquivariantDiagram D (ModuleCat.{u} R)) q).inv.app K) := by
  simp [etaleAssociatedVaryingDerivedHomologyIso,
    Langlands.Cohomology.exactDerivedHomologyIsoOnComplexes,
    etaleAssociatedVaryingDerivedFactors, etaleAssociatedVaryingHomologyIso,
    etaleAssociatedVaryingComplexFunctor]
  rfl

/-- The comparison intertwines every derived coefficient morphism. -/
@[reassoc]
theorem etaleAssociatedVaryingDerivedHomologyIso_naturality (q : ℤ)
    {K L : DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R))} (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor
        (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q).map
          ((etaleAssociatedVaryingDerivedFunctor X Y hY).map f) ≫
        (etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app L =
      (etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app K ≫
        (etaleAssociatedVaryingSystemFunctor X Y hY).map
          ((DerivedCategory.homologyFunctor
            (EquivariantDiagram D (ModuleCat.{u} R)) q).map f) :=
  (etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.naturality f

/-- The comparison retains the genuine transition maps at every cover arrow. -/
@[reassoc]
theorem etaleAssociatedVaryingDerivedHomologyIso_transition (q : ℤ)
    (K : DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R)))
    {i j : J} (a : i ⟶ j) :
    ((DerivedCategory.homologyFunctor
        (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q).obj
          ((etaleAssociatedVaryingDerivedFunctor X Y hY).obj K)).map a ≫
        ((etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app K).app j =
      ((etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app K).app i ≫
        (etaleAssociatedTransition X Y hY a).app
          ((DerivedCategory.homologyFunctor
            (EquivariantDiagram D (ModuleCat.{u} R)) q).obj K) :=
  ((etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app K).naturality a

section Evaluation

variable [HasDerivedCategory.{wE} (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))]

/-- Exact association at a chosen cover on actual unbounded derived categories. -/
def etaleAssociatedAtDerivedFunctor (j : J) :
    DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) := by
  have := etaleAssociatedAtPreservesFiniteLimits (R := R) X Y hY j
  have := etaleAssociatedAtPreservesFiniteColimits (R := R) X Y hY j
  exact (etaleAssociatedAt X Y j).mapDerivedCategory

instance (j : J) : (etaleAssociatedAtDerivedFunctor (R := R) X Y hY j).CommShift ℤ := by
  dsimp [etaleAssociatedAtDerivedFunctor]
  infer_instance

instance (j : J) : (etaleAssociatedAtDerivedFunctor (R := R) X Y hY j).IsTriangulated := by
  dsimp [etaleAssociatedAtDerivedFunctor]
  infer_instance

/-- Exact cover evaluation of derived association agrees with derived association
at that cover. -/
def etaleAssociatedVaryingDerivedEvaluationIso (j : J) :
    etaleAssociatedVaryingDerivedFunctor (R := R) X Y hY ⋙
        ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j).mapDerivedCategory ≅
      etaleAssociatedAtDerivedFunctor X Y hY j := by
  exact Functor.mapDerivedCategoryCompIso
    (etaleAssociatedVaryingSystemFunctor X Y hY)
    ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j)

/-- Homology after exact derived cover evaluation is the sheaf associated to
derived coefficient homology at that cover. -/
def etaleAssociatedVaryingDerivedEvaluationHomologyIso (q : ℤ) (j : J) :
    (etaleAssociatedVaryingDerivedFunctor (R := R) X Y hY ⋙
        ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j).mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) q ≅
      DerivedCategory.homologyFunctor (EquivariantDiagram D (ModuleCat.{u} R)) q ⋙
        etaleAssociatedAt X Y j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Langlands.Cohomology.exactDerivedHomologyIso
        ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j) q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleAssociatedVaryingDerivedHomologyIso X Y hY q) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleAssociatedVaryingEvaluationIso X Y hY j)

/-- The coverwise comparison first computes exact-evaluation homology, then
evaluates the whole-diagram association comparison. -/
@[reassoc]
theorem etaleAssociatedVaryingDerivedEvaluationHomologyIso_hom_app (q : ℤ) (j : J)
    (K : DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R))) :
    (etaleAssociatedVaryingDerivedEvaluationHomologyIso X Y hY q j).hom.app K =
      (Langlands.Cohomology.exactDerivedHomologyIso
        ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j) q).hom.app
          ((etaleAssociatedVaryingDerivedFunctor X Y hY).obj K) ≫
        ((etaleAssociatedVaryingDerivedHomologyIso X Y hY q).hom.app K).app j := by
  simp [etaleAssociatedVaryingDerivedEvaluationHomologyIso,
    etaleAssociatedVaryingEvaluationIso, NatIso.ofComponents]
  erw [Category.comp_id]
  rfl

end Evaluation

end Langlands.Shimura.Coefficients
