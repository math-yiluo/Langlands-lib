import Langlands.Shimura.Coefficients.AssociatedPowerHomology
import Langlands.Cohomology.DivisibleSystem.InverseLimit

/-! # Coverwise homology of associated power complexes -/

noncomputable section

universe u uJ vJ uι

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]
variable {J : Type uJ} [Category.{vJ} J]
variable (X : Scheme.{u}) {ι : Type uι} (c : ComplexShape ι) (i : ι) (j : J)

/-- Evaluate an actual complex of small-etale sheaf diagrams at one cover. -/
abbrev etaleSheafComplexEvaluation :
    HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c :=
  ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j).mapHomologicalComplex c

/-- Exact evaluation identifies diagram homology with homology of the evaluated complex. -/
def etaleSheafHomologyEvaluationIso :
    etaleSheafDiagramHomologyFunctor (R := R) X c i ⋙
        (evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j ≅
      etaleSheafComplexEvaluation X c j ⋙
        HomologicalComplex.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i :=
  (Langlands.Cohomology.mapHomologicalComplexHomologyIso
    ((evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j) c i).symm

variable (F : ℕᵒᵖ ⥤
  HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c)

/-- The homology evaluation isomorphisms form an isomorphism of full power systems. -/
def etaleSheafHomologySystemEvaluationIso :
    F ⋙ etaleSheafDiagramHomologyFunctor X c i ⋙
        (evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j ≅
      F ⋙ etaleSheafComplexEvaluation X c j ⋙
        HomologicalComplex.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i :=
  Functor.isoWhiskerLeft F (etaleSheafHomologyEvaluationIso X c i j)

/-- Evaluate the ordinary limit of diagram homology as the limit of coverwise homology. -/
def etaleSheafHomologyLimitEvaluationIso :
    (limit (F ⋙ etaleSheafDiagramHomologyFunctor X c i)).obj j ≅
      limit (F ⋙ etaleSheafComplexEvaluation X c j ⋙
        HomologicalComplex.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) :=
  limitObjIsoLimitCompEvaluation _ j ≪≫
    HasLimit.isoOfNatIso (etaleSheafHomologySystemEvaluationIso X c i j F)

@[reassoc (attr := simp)]
theorem etaleSheafHomologyLimitEvaluationIso_hom_π (n : ℕᵒᵖ) :
    (etaleSheafHomologyLimitEvaluationIso X c i j F).hom ≫
        limit.π (F ⋙ etaleSheafComplexEvaluation X c j ⋙
          HomologicalComplex.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) n =
      (limit.π (F ⋙ etaleSheafDiagramHomologyFunctor X c i) n).app j ≫
        (etaleSheafHomologyEvaluationIso X c i j).hom.app (F.obj n) := by
  dsimp only [etaleSheafHomologyLimitEvaluationIso, Iso.trans_hom]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π,
    ← Category.assoc, limitObjIsoLimitCompEvaluation_hom_π]
  rfl

/-- Homology of the evaluated complex limit is the evaluation of its diagram homology. -/
def etaleSheafLimitHomologyEvaluationIso :
    ((etaleSheafDiagramHomologyFunctor X c i).obj (limit F)).obj j ≅
      (HomologicalComplex.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i).obj
          (limit (F ⋙ etaleSheafComplexEvaluation X c j)) :=
  (etaleSheafHomologyEvaluationIso X c i j).app (limit F) ≪≫
    (HomologicalComplex.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i).mapIso
        (preservesLimitIso (etaleSheafComplexEvaluation X c j) F)

/-- The ordinary-limit evaluation isomorphism is natural in maps of complex systems. -/
theorem etaleSheafHomologyLimitEvaluationIso_naturality
    {G : ℕᵒᵖ ⥤
      HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c}
    (α : F ⟶ G) :
    (limMap (Functor.whiskerRight α
        (etaleSheafDiagramHomologyFunctor X c i))).app j ≫
        (etaleSheafHomologyLimitEvaluationIso X c i j G).hom =
      (etaleSheafHomologyLimitEvaluationIso X c i j F).hom ≫
        limMap (Functor.whiskerRight α
          (etaleSheafComplexEvaluation X c j ⋙
            HomologicalComplex.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i)) := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, etaleSheafHomologyLimitEvaluationIso_hom_π,
    limMap_π]
  rw [etaleSheafHomologyLimitEvaluationIso_hom_π_assoc]
  rw [← Category.assoc, ← NatTrans.comp_app, limMap_π, NatTrans.comp_app,
    Category.assoc]
  exact congrArg
    (fun f => (limit.π (F ⋙ etaleSheafDiagramHomologyFunctor X c i) n).app j ≫ f)
    ((etaleSheafHomologyEvaluationIso X c i j).hom.naturality (α.app n))

/-- Evaluation transports the canonical homology/limit map to its coverwise counterpart. -/
theorem etaleSheafLimitHomologyComparison_evaluation :
    (limit.post F (etaleSheafDiagramHomologyFunctor X c i)).app j ≫
        (etaleSheafHomologyLimitEvaluationIso X c i j F).hom =
      (etaleSheafLimitHomologyEvaluationIso X c i j F).hom ≫
        limit.post (F ⋙ etaleSheafComplexEvaluation X c j)
          (HomologicalComplex.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) := by
  apply limit.hom_ext
  intro n
  rw [Category.assoc, etaleSheafHomologyLimitEvaluationIso_hom_π,
    ← Category.assoc, ← NatTrans.comp_app, limit.post_π,
    Category.assoc]
  erw [limit.post_π]
  simp only [etaleSheafLimitHomologyEvaluationIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp, preservesLimitIso_hom_π]
  exact (etaleSheafHomologyEvaluationIso X c i j).hom.naturality (limit.π F n)

section Associated

variable (I : Ideal R) {D : J ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))
variable (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)

/-- The actual sheaf-power homology limit evaluated at a cover. -/
def etaleAssociatedSheafPowerHomologyLimitEvaluationIso :
    (((etaleAssociatedSheafPowerHomologyLimit I X Y hY c i).obj K).obj j) ≅
      limit ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K ⋙
        etaleSheafComplexEvaluation X c j ⋙
          HomologicalComplex.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) :=
  etaleSheafHomologyLimitEvaluationIso X c i j
    ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K)

/-- The actual associated coefficient-power homology limit evaluated at a cover. -/
def etaleAssociatedPowerHomologyLimitEvaluationIso :
    (((etaleAssociatedPowerHomologyLimit I X Y hY c i).obj K).obj j) ≅
      limit ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K ⋙
        etaleSheafComplexEvaluation X c j ⋙
          HomologicalComplex.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) :=
  etaleSheafHomologyLimitEvaluationIso X c i j
    ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K)

/-- The published sheaf-power comparison is the canonical coverwise homology/limit map. -/
theorem etaleAssociatedSheafPowerLimitHomologyComparison_evaluation :
    ((etaleAssociatedSheafPowerLimitHomologyComparison I X Y hY c i).app K).app j ≫
        (etaleAssociatedSheafPowerHomologyLimitEvaluationIso X c i j I Y hY K).hom =
      (etaleSheafLimitHomologyEvaluationIso X c i j
          ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K)).hom ≫
        limit.post
          (((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K) ⋙
            etaleSheafComplexEvaluation X c j)
          (HomologicalComplex.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) :=
  etaleSheafLimitHomologyComparison_evaluation X c i j
    ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K)

/-- The published coefficient-power comparison is the canonical coverwise map. -/
theorem etaleAssociatedPowerLimitHomologyComparison_evaluation :
    ((etaleAssociatedPowerLimitHomologyComparison I X Y hY c i).app K).app j ≫
        (etaleAssociatedPowerHomologyLimitEvaluationIso X c i j I Y hY K).hom =
      (etaleSheafLimitHomologyEvaluationIso X c i j
          ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K)).hom ≫
        limit.post
          (((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) ⋙
            etaleSheafComplexEvaluation X c j)
          (HomologicalComplex.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) :=
  etaleSheafLimitHomologyComparison_evaluation X c i j
    ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K)

/-- The comparison of both homology limits is the limit of the actual coverwise maps. -/
theorem etaleAssociatedPowerHomologyLimitComparison_evaluation :
    ((etaleAssociatedPowerHomologyLimitComparison I X Y hY c i).app K).app j ≫
        (etaleAssociatedPowerHomologyLimitEvaluationIso X c i j I Y hY K).hom =
      (etaleAssociatedSheafPowerHomologyLimitEvaluationIso X c i j I Y hY K).hom ≫
        limMap (Functor.whiskerRight
          ((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K)
          (etaleSheafComplexEvaluation X c j ⋙
            HomologicalComplex.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i)) :=
  etaleSheafHomologyLimitEvaluationIso_naturality X c i j
    ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K)
    ((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K)

/-- In every cover and power the sheaf unit gives homology of the genuine sheaf quotient. -/
@[reassoc (attr := simp)]
theorem etaleAssociatedSheafPowerHomologyLimitUnit_evaluation_projection (n : ℕ) :
    ((etaleAssociatedSheafPowerHomologyLimitUnit I X Y hY c i).app K).app j ≫
        (etaleAssociatedSheafPowerHomologyLimitEvaluationIso X c i j I Y hY K).hom ≫
          limit.π ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K ⋙
            etaleSheafComplexEvaluation X c j ⋙
              HomologicalComplex.homologyFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) (op n) =
      (etaleSheafHomologyEvaluationIso X c i j).hom.app
          ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) ≫
        HomologicalComplex.homologyMap
          ((etaleSheafComplexEvaluation X c j).map
            ((sheafDiagramComplexPowerUnit X.smallEtaleTopology I J c n).app
              ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K))) i := by
  rw [etaleAssociatedSheafPowerHomologyLimitEvaluationIso,
    etaleSheafHomologyLimitEvaluationIso_hom_π, ← Category.assoc,
    ← NatTrans.comp_app]
  erw [etaleAssociatedSheafPowerHomologyLimitUnit_π]
  exact (etaleSheafHomologyEvaluationIso X c i j).hom.naturality
    ((sheafDiagramComplexPowerUnit X.smallEtaleTopology I J c n).app
      ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K))

/-- In every cover and power the coefficient unit gives homology of its actual quotient map. -/
@[reassoc (attr := simp)]
theorem etaleAssociatedPowerHomologyLimitUnit_evaluation_projection (n : ℕ) :
    ((etaleAssociatedPowerHomologyLimitUnit I X Y hY c i).app K).app j ≫
        (etaleAssociatedPowerHomologyLimitEvaluationIso X c i j I Y hY K).hom ≫
          limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K ⋙
            etaleSheafComplexEvaluation X c j ⋙
              HomologicalComplex.homologyFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c i) (op n) =
      (etaleSheafHomologyEvaluationIso X c i j).hom.app
          ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) ≫
        HomologicalComplex.homologyMap
          ((etaleSheafComplexEvaluation X c j).map
            ((etaleAssociatedVaryingComplexFunctor X Y hY c).map
              ((coefficientComplexPowerUnit I c n).app K))) i := by
  rw [etaleAssociatedPowerHomologyLimitEvaluationIso,
    etaleSheafHomologyLimitEvaluationIso_hom_π, ← Category.assoc,
    ← NatTrans.comp_app]
  erw [etaleAssociatedPowerHomologyLimitUnit_π]
  exact (etaleSheafHomologyEvaluationIso X c i j).hom.naturality
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).map
      ((coefficientComplexPowerUnit I c n).app K))

end Associated

end Langlands.Shimura.Coefficients
