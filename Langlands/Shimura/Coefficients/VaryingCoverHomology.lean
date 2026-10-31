import Langlands.Cohomology.DiagramHomology
import Langlands.Shimura.Coefficients.VaryingCoverExact
import Langlands.Shimura.Coefficients.AssociatedPowerHomologyEvaluation

/-! # Coverwise homology of varying-cover associated complexes -/

noncomputable section

universe u uJ vJ uι

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))
variable {ι : Type uι} (c : ComplexShape ι)

/-- The actual coverwise homologies form the diagram associated to coefficient homology,
with the given varying-cover transition chain maps. -/
def etaleAssociatedVaryingCoverwiseHomologyIso (q : ι) :
    etaleAssociatedVaryingComplexSystemFunctor (R := R) X Y hY c ⋙
        (Functor.whiskeringRight J
          (HomologicalComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c)
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj
            (HomologicalComplex.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c q) ≅
      HomologicalComplex.homologyFunctor
          (EquivariantDiagram D (ModuleCat.{u} R)) c q ⋙
        etaleAssociatedVaryingSystemFunctor X Y hY :=
  Functor.isoWhiskerLeft (etaleAssociatedVaryingComplexFunctor X Y hY c)
      (Langlands.Cohomology.diagramHomologyIso c q) ≪≫
    etaleAssociatedVaryingHomologyIso X Y hY c q

/-- The coverwise comparison factors through the previously constructed evaluation
isomorphism and the whole-diagram homology comparison. -/
@[simp]
theorem etaleAssociatedVaryingCoverwiseHomologyIso_hom_app
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (q : ι) (j : J) :
    ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.app K).app j =
      (etaleSheafHomologyEvaluationIso X c q j).inv.app
          ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) ≫
        ((etaleAssociatedVaryingHomologyIso X Y hY c q).hom.app K).app j := rfl

/-- Homology of every actual cover-transition chain map intertwines the comparison. -/
@[reassoc]
theorem etaleAssociatedVaryingCoverwiseHomologyIso_transition
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (q : ι) {i j : J} (a : i ⟶ j) :
    HomologicalComplex.homologyMap
        (((etaleAssociatedVaryingComplexSystemFunctor X Y hY c).obj K).map a) q ≫
        ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.app K).app j =
      ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.app K).app i ≫
        (etaleAssociatedTransition X Y hY a).app (K.homology q) :=
  ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.app K).naturality a

/-- At each cover the comparison also intertwines every coefficient chain map. -/
@[reassoc]
theorem etaleAssociatedVaryingCoverwiseHomologyIso_naturality
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (q : ι) (j : J) :
    HomologicalComplex.homologyMap
        (((etaleAssociatedVaryingComplexSystemFunctor X Y hY c).map f).app j) q ≫
        ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.app L).app j =
      ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.app K).app j ≫
        (etaleAssociatedAt X Y j).map (HomologicalComplex.homologyMap f q) :=
  NatTrans.congr_app
    ((etaleAssociatedVaryingCoverwiseHomologyIso X Y hY c q).hom.naturality f) j

/-- A coefficient quasi-isomorphism induces a quasi-isomorphism at every actual cover. -/
theorem etaleAssociatedVaryingComplexSystemFunctor_preserves_quasiIso
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) [QuasiIso f] (j : J) :
    QuasiIso
      (((etaleAssociatedVaryingComplexSystemFunctor (R := R) X Y hY c).map f).app j) := by
  have := etaleAssociatedVaryingComplexFunctor_preserves_quasiIso X Y hY c f
  exact (HomologicalComplex.quasiIso_iff_evaluation
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).map f)).1 inferInstance j

end Langlands.Shimura.Coefficients
