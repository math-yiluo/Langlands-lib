import Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization
import Langlands.Shimura.Coefficients.VaryingCoverDerived
import Langlands.Sheaf.SliceExact
import Langlands.Geometry.EtaleSlice

/-! # Source-local trivialization on actual derived categories -/

noncomputable section

universe u uI vI wC wS

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) (k : I)

instance etaleSlicePullback_additive (V : X.Etale) :
    (X.smallEtaleTopology.overPullback (ModuleCat.{u} R) V).Additive where
  map_add := by
    intro F G f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

instance etaleConstantSourceSystemFunctor_additive :
    (etaleConstantSourceSystemFunctor (R := R) X Y k).Additive := by
  unfold etaleConstantSourceSystemFunctor
  infer_instance

instance etaleConstantSourceSystemFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (etaleConstantSourceSystemFunctor (R := R) X Y k) := by
  have : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)) := by
    unfold constantSheaf
    infer_instance
  refine ⟨?_⟩
  intro K _ _
  unfold etaleConstantSourceSystemFunctor
  infer_instance

instance etaleConstantSourceSystemFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (etaleConstantSourceSystemFunctor (R := R) X Y k) := by
  have : PreservesColimitsOfSize.{0,0}
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
    (constantSheafAdj _ _ (etaleIdIsTerminal X)).leftAdjoint_preservesColimits
  refine ⟨?_⟩
  intro K _ _
  unfold etaleConstantSourceSystemFunctor
  infer_instance

instance etaleAssociatedSourceSystemFunctor_additive :
    (etaleAssociatedSourceSystemFunctor (R := R) X Y hY k).Additive := by
  unfold etaleAssociatedSourceSystemFunctor
  infer_instance

/-- Source-local association is exact by its proved trivialization with the
exact constant-source construction. -/
theorem etaleAssociatedSourceSystemFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (etaleAssociatedSourceSystemFunctor (R := R) X Y hY k) :=
  preservesFiniteLimits_of_natIso
    (etaleAssociatedSourceTrivializationFunctor X Y hY k).symm

theorem etaleAssociatedSourceSystemFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (etaleAssociatedSourceSystemFunctor (R := R) X Y hY k) :=
  preservesFiniteColimits_of_natIso
    (etaleAssociatedSourceTrivializationFunctor X Y hY k).symm

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

/-- The original invariant-section formula is retained in each cochain degree
and at every reachable cover. -/
@[simp]
theorem etaleAssociatedSourceTrivialization_complex_hom_f_app
    (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ)
    (q : ℤ) (i : Under k) :
    ((((etaleAssociatedSourceTrivializationFunctor X Y hY k).hom.mapHomologicalComplex
        (ComplexShape.up ℤ)).app K).f q).app i =
      etaleAssociatedEvaluationAlong X Y (K.X q) i.right (Y.obj.map i.hom) := rfl

variable [HasDerivedCategory.{wC} (EquivariantDiagram D (ModuleCat.{u} R))]
variable [HasDerivedCategory.{wS}
  (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R))]

/-- Actual derived association followed by localization of the reachable diagram
on the fixed source torsor. -/
def etaleAssociatedSourceDerivedFunctor :
    DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R)) ⥤
      DerivedCategory
        (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R)) :=
  (etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategory

/-- The original coefficient diagram, made constant on the same source slice,
on actual unbounded derived categories. -/
def etaleConstantSourceDerivedFunctor :
    DerivedCategory (EquivariantDiagram D (ModuleCat.{u} R)) ⥤
      DerivedCategory
        (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R)) :=
  (etaleConstantSourceSystemFunctor X Y k).mapDerivedCategory

instance : (etaleAssociatedSourceDerivedFunctor (R := R) X Y hY k).CommShift ℤ := by
  dsimp [etaleAssociatedSourceDerivedFunctor]
  infer_instance

instance : (etaleAssociatedSourceDerivedFunctor (R := R) X Y hY k).IsTriangulated := by
  dsimp [etaleAssociatedSourceDerivedFunctor]
  infer_instance

instance : (etaleConstantSourceDerivedFunctor (R := R) X Y k).CommShift ℤ := by
  dsimp [etaleConstantSourceDerivedFunctor]
  infer_instance

instance : (etaleConstantSourceDerivedFunctor (R := R) X Y k).IsTriangulated := by
  dsimp [etaleConstantSourceDerivedFunctor]
  infer_instance

/-- The proved invariant-section evaluation isomorphism descends through
quasi-isomorphism localization, naturally in every derived coefficient morphism. -/
def etaleAssociatedSourceDerivedTrivialization :
    etaleAssociatedSourceDerivedFunctor (R := R) X Y hY k ≅
      etaleConstantSourceDerivedFunctor X Y k := by
  dsimp [etaleAssociatedSourceDerivedFunctor, etaleConstantSourceDerivedFunctor]
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (EquivariantDiagram D (ModuleCat.{u} R))
      (ComplexShape.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (etaleAssociatedSourceTrivializationFunctor X Y hY k)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The descended map is the lift of the original evaluation transformation. -/
theorem etaleAssociatedSourceDerivedTrivialization_hom :
    (etaleAssociatedSourceDerivedTrivialization (R := R) X Y hY k).hom =
      (etaleAssociatedSourceTrivializationFunctor X Y hY k).hom.mapDerivedCategory := rfl

instance : NatTrans.CommShift
    (etaleAssociatedSourceDerivedTrivialization (R := R) X Y hY k).hom ℤ := by
  rw [etaleAssociatedSourceDerivedTrivialization_hom]
  exact inferInstanceAs (NatTrans.CommShift
    ((etaleAssociatedSourceTrivializationFunctor X Y hY k).hom.mapDerivedCategory) ℤ)

/-- On cochain representatives the derived map is precisely localization of
termwise invariant evaluation, conjugated by the canonical factorization maps. -/
@[reassoc]
theorem etaleAssociatedSourceDerivedTrivialization_hom_app_Q_obj
    (K : CochainComplex (EquivariantDiagram D (ModuleCat.{u} R)) ℤ) :
    (etaleAssociatedSourceDerivedTrivialization X Y hY k).hom.app
        (DerivedCategory.Q.obj K) =
      (etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          (((etaleAssociatedSourceTrivializationFunctor X Y hY k).hom.mapHomologicalComplex
            (ComplexShape.up ℤ)).app K) ≫
        (etaleConstantSourceSystemFunctor X Y k).mapDerivedCategoryFactors.inv.app K :=
  NatTrans.mapDerivedCategory_app_Q_obj _ K

/-- In a single degree the derived comparison recovers the same evaluation
isomorphism on ordinary source-local coefficient diagrams. -/
@[reassoc]
theorem etaleAssociatedSourceDerivedTrivialization_hom_app_single
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (q : ℤ) :
    (etaleAssociatedSourceDerivedTrivialization X Y hY k).hom.app
        ((DerivedCategory.singleFunctor (EquivariantDiagram D (ModuleCat.{u} R)) q).obj M) =
      ((etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategorySingleFunctor q).hom.app M ≫
        (DerivedCategory.singleFunctor
          (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} R)) q).map
          (etaleAssociatedSourceTrivialization X Y hY k M).hom ≫
        ((etaleConstantSourceSystemFunctor X Y k).mapDerivedCategorySingleFunctor q).inv.app M :=
  NatTrans.mapDerivedCategory_app_singleFunctor_obj _ M q

end Langlands.Shimura.Coefficients
