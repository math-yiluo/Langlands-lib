import Langlands.Cohomology.ExactDerivedSquare
import Langlands.Sheaf.SourceSliceExact
import Langlands.Shimura.Coefficients.VaryingCoverSourceChange
import Langlands.Shimura.Coefficients.VaryingCoverDerivedLocalTrivialization

/-! # Source changes and invariant evaluation on actual derived categories -/

noncomputable section

universe u uI vI wC wK wL wM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.Sheaf
open Langlands.Cohomology

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
variable {k l : I}

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

/-- In every cochain degree and at every reachable cover, the associated
comparison is the identity on the actual common sheaf sections. -/
@[simp] theorem etaleAssociatedSourceChange_complex_hom_f_app_hom_app
    (f : k ⟶ l) (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ) (q : ℤ)
    (i : Under l) (V : (Over (Y.obj.obj k))ᵒᵖ) :
    (((((etaleAssociatedSourceChangeFunctorIso X Y hY f).hom.mapHomologicalComplex
        (ComplexShape.up ℤ)).app K).f q).app i).hom.app V = 𝟙 _ := rfl

@[simp] theorem etaleConstantSourceChange_complex_hom_f_app_hom_app
    (f : k ⟶ l) (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ) (q : ℤ)
    (i : Under l) (V : (Over (Y.obj.obj k))ᵒᵖ) :
    (((((etaleConstantSourceChangeFunctorIso X Y f).hom.mapHomologicalComplex
        (ComplexShape.up ℤ)).app K).f q).app i).hom.app V = 𝟙 _ := rfl

variable [HasDerivedCategory.{wK}
  (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R))]
variable [HasDerivedCategory.{wL}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj l)) (ModuleCat.{u} R))]
variable [HasDerivedCategory.{wM}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R))]

/-- Restrict a whole source-local sheaf diagram on actual derived categories. -/
def etaleSourceRestrictionDerivedFunctor (f : k ⟶ l) :
    DerivedCategory.{wL}
        (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj l)) (ModuleCat.{u} R)) ⥤
      DerivedCategory.{wM}
        (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R)) :=
  (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategory

/-- Reindex the whole source-local diagram by composition of outgoing arrows. -/
def etaleSourceReindexDerivedFunctor (f : k ⟶ l) :
    DerivedCategory.{wK}
        (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R)) ⥤
      DerivedCategory.{wM}
        (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R)) :=
  (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategory

instance (f : k ⟶ l) :
    (etaleSourceRestrictionDerivedFunctor (R := R) X Y f).CommShift ℤ := by
  dsimp [etaleSourceRestrictionDerivedFunctor]
  infer_instance

instance (f : k ⟶ l) :
    (etaleSourceRestrictionDerivedFunctor (R := R) X Y f).IsTriangulated := by
  dsimp [etaleSourceRestrictionDerivedFunctor]
  infer_instance

instance (f : k ⟶ l) :
    (etaleSourceReindexDerivedFunctor (R := R) X Y f).CommShift ℤ := by
  dsimp [etaleSourceReindexDerivedFunctor]
  infer_instance

instance (f : k ⟶ l) :
    (etaleSourceReindexDerivedFunctor (R := R) X Y f).IsTriangulated := by
  dsimp [etaleSourceReindexDerivedFunctor]
  infer_instance

variable [HasDerivedCategory.{wC} (EquivariantDiagram D (ModuleCat.{u} R))]

/-- The actual associated source-change comparison descends through
quasi-isomorphism localization of the whole coefficient diagram category. -/
def etaleAssociatedSourceDerivedChangeIso (f : k ⟶ l) :
    etaleAssociatedSourceDerivedFunctor (R := R) X Y hY l ⋙
        etaleSourceRestrictionDerivedFunctor X Y f ≅
      etaleAssociatedSourceDerivedFunctor X Y hY k ⋙
        etaleSourceReindexDerivedFunctor X Y f :=
  exactDerivedSquareIso _ _ _ _ (etaleAssociatedSourceChangeFunctorIso X Y hY f)

/-- The same derived source-change comparison for the original constant
coefficient diagram. -/
def etaleConstantSourceDerivedChangeIso (f : k ⟶ l) :
    etaleConstantSourceDerivedFunctor (R := R) X Y l ⋙
        etaleSourceRestrictionDerivedFunctor X Y f ≅
      etaleConstantSourceDerivedFunctor X Y k ⋙
        etaleSourceReindexDerivedFunctor X Y f :=
  exactDerivedSquareIso _ _ _ _ (etaleConstantSourceChangeFunctorIso X Y f)

instance (f : k ⟶ l) : NatTrans.CommShift
    (etaleAssociatedSourceDerivedChangeIso (R := R) X Y hY f).hom ℤ := by
  dsimp only [etaleAssociatedSourceDerivedChangeIso]
  infer_instance

instance (f : k ⟶ l) : NatTrans.CommShift
    (etaleConstantSourceDerivedChangeIso (R := R) X Y f).hom ℤ := by
  dsimp only [etaleConstantSourceDerivedChangeIso]
  infer_instance

/-- The derived associated comparison recovers localization of the actual
termwise source change, through the canonical exact-functor factors. -/
@[reassoc] theorem etaleAssociatedSourceDerivedChangeIso_hom_app_Q_obj
    (f : k ⟶ l) (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ) :
    (etaleAssociatedSourceDerivedChangeIso X Y hY f).hom.app (DerivedCategory.Q.obj K) =
      (etaleSourceRestrictionDerivedFunctor X Y f).map
          ((etaleAssociatedSourceSystemFunctor X Y hY l).mapDerivedCategoryFactors.hom.app K) ≫
        (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategoryFactors.hom.app
          (((etaleAssociatedSourceSystemFunctor X Y hY l).mapHomologicalComplex _).obj K) ≫
        DerivedCategory.Q.map
          (((etaleAssociatedSourceChangeFunctorIso X Y hY f).hom.mapHomologicalComplex
            (ComplexShape.up ℤ)).app K) ≫
        (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategoryFactors.inv.app
          (((etaleAssociatedSourceSystemFunctor X Y hY k).mapHomologicalComplex _).obj K) ≫
        (etaleSourceReindexDerivedFunctor X Y f).map
          ((etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategoryFactors.inv.app K) :=
  exactDerivedSquareIso_hom_app_Q_obj _ _ _ _ _ K

@[reassoc] theorem etaleConstantSourceDerivedChangeIso_hom_app_Q_obj
    (f : k ⟶ l) (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ) :
    (etaleConstantSourceDerivedChangeIso X Y f).hom.app (DerivedCategory.Q.obj K) =
      (etaleSourceRestrictionDerivedFunctor X Y f).map
          ((etaleConstantSourceSystemFunctor X Y l).mapDerivedCategoryFactors.hom.app K) ≫
        (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategoryFactors.hom.app
          (((etaleConstantSourceSystemFunctor X Y l).mapHomologicalComplex _).obj K) ≫
        DerivedCategory.Q.map
          (((etaleConstantSourceChangeFunctorIso X Y f).hom.mapHomologicalComplex
            (ComplexShape.up ℤ)).app K) ≫
        (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategoryFactors.inv.app
          (((etaleConstantSourceSystemFunctor X Y k).mapHomologicalComplex _).obj K) ≫
        (etaleSourceReindexDerivedFunctor X Y f).map
          ((etaleConstantSourceSystemFunctor X Y k).mapDerivedCategoryFactors.inv.app K) :=
  exactDerivedSquareIso_hom_app_Q_obj _ _ _ _ _ K

/-- The derived comparison recovers the ordinary associated source change in
every single degree, with the canonical composite single-degree comparisons. -/
@[reassoc] theorem etaleAssociatedSourceDerivedChangeIso_hom_app_single
    (f : k ⟶ l) (M : EquivariantDiagram D (ModuleCat.{u} R)) (q : ℤ) :
    (etaleAssociatedSourceDerivedChangeIso X Y hY f).hom.app
        ((DerivedCategory.singleFunctor (EquivariantDiagram D (ModuleCat.{u} R)) q).obj M) =
      (etaleSourceRestrictionDerivedFunctor X Y f).map
          (((etaleAssociatedSourceSystemFunctor X Y hY l).mapDerivedCategorySingleFunctor q).hom.app M) ≫
        ((sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategorySingleFunctor q).hom.app
          ((etaleAssociatedSourceSystemFunctor X Y hY l).obj M) ≫
        (DerivedCategory.singleFunctor (Under l ⥤ Sheaf ((X.smallEtaleTopology).over (Y.obj.obj k)) (ModuleCat.{u} R)) q).map
          ((etaleAssociatedSourceChangeFunctorIso X Y hY f).hom.app M) ≫
        ((sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategorySingleFunctor q).inv.app
          ((etaleAssociatedSourceSystemFunctor X Y hY k).obj M) ≫
        (etaleSourceReindexDerivedFunctor X Y f).map
          (((etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategorySingleFunctor q).inv.app M) :=
  exactDerivedSquareIso_hom_app_single
    (etaleAssociatedSourceSystemFunctor X Y hY l)
    (etaleAssociatedSourceSystemFunctor X Y hY k)
    (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f)
    (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f)
    (etaleAssociatedSourceChangeFunctorIso X Y hY f) M q

@[reassoc] theorem etaleConstantSourceDerivedChangeIso_hom_app_single
    (f : k ⟶ l) (M : EquivariantDiagram D (ModuleCat.{u} R)) (q : ℤ) :
    (etaleConstantSourceDerivedChangeIso X Y f).hom.app
        ((DerivedCategory.singleFunctor (EquivariantDiagram D (ModuleCat.{u} R)) q).obj M) =
      (etaleSourceRestrictionDerivedFunctor X Y f).map
          (((etaleConstantSourceSystemFunctor X Y l).mapDerivedCategorySingleFunctor q).hom.app M) ≫
        ((sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategorySingleFunctor q).hom.app
          ((etaleConstantSourceSystemFunctor X Y l).obj M) ≫
        (DerivedCategory.singleFunctor (Under l ⥤ Sheaf ((X.smallEtaleTopology).over (Y.obj.obj k)) (ModuleCat.{u} R)) q).map
          ((etaleConstantSourceChangeFunctorIso X Y f).hom.app M) ≫
        ((sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f).mapDerivedCategorySingleFunctor q).inv.app
          ((etaleConstantSourceSystemFunctor X Y k).obj M) ≫
        (etaleSourceReindexDerivedFunctor X Y f).map
          (((etaleConstantSourceSystemFunctor X Y k).mapDerivedCategorySingleFunctor q).inv.app M) :=
  exactDerivedSquareIso_hom_app_single
    (etaleConstantSourceSystemFunctor X Y l)
    (etaleConstantSourceSystemFunctor X Y k)
    (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f)
    (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} R) Y.obj f)
    (etaleConstantSourceChangeFunctorIso X Y f) M q

/-- The actual invariant-evaluation trivialization commutes with source change
as an equality of natural transformations on the entire derived category. -/
@[reassoc] theorem etaleAssociatedSourceDerivedTrivialization_sourceChange
    (f : k ⟶ l) :
    Functor.whiskerRight (etaleAssociatedSourceDerivedTrivialization (R := R) X Y hY l).hom
        (etaleSourceRestrictionDerivedFunctor X Y f) ≫
      (etaleConstantSourceDerivedChangeIso X Y f).hom =
    (etaleAssociatedSourceDerivedChangeIso X Y hY f).hom ≫
      Functor.whiskerRight (etaleAssociatedSourceDerivedTrivialization X Y hY k).hom
        (etaleSourceReindexDerivedFunctor X Y f) :=
  exactDerivedSquareIso_naturality _ _ _ _ _ _
    (etaleAssociatedSourceChangeFunctorIso X Y hY f)
    (etaleConstantSourceChangeFunctorIso X Y f)
    (etaleAssociatedSourceTrivializationFunctor X Y hY l).hom
    (etaleAssociatedSourceTrivializationFunctor X Y hY k).hom
    (etaleAssociatedSourceTrivializationFunctor_sourceChange X Y hY f)

/-- The same compatibility evaluated at any derived coefficient object. -/
@[reassoc] theorem etaleAssociatedSourceDerivedTrivialization_sourceChange_app
    (f : k ⟶ l) (K : DerivedCategory.{wC} (EquivariantDiagram D (ModuleCat.{u} R))) :
    (etaleSourceRestrictionDerivedFunctor X Y f).map
        ((etaleAssociatedSourceDerivedTrivialization X Y hY l).hom.app K) ≫
      (etaleConstantSourceDerivedChangeIso X Y f).hom.app K =
    (etaleAssociatedSourceDerivedChangeIso X Y hY f).hom.app K ≫
      (etaleSourceReindexDerivedFunctor X Y f).map
        ((etaleAssociatedSourceDerivedTrivialization X Y hY k).hom.app K) :=
  congr_app (etaleAssociatedSourceDerivedTrivialization_sourceChange X Y hY f) K

end Langlands.Shimura.Coefficients
