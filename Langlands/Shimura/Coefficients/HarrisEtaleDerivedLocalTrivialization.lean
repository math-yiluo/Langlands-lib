import Langlands.Shimura.Coefficients.HarrisEtaleLocalTrivialization
import Langlands.Shimura.Coefficients.VaryingCoverDerivedLocalTrivialization

/-! # Harris coefficient trivialization on actual derived categories -/

noncomputable section

universe u wC wS wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Langlands.Global

private theorem isoConjugation
    {B : Type*} [Category* B] {x₁ x₂ y₁ y₂ : B}
    (α : x₁ ≅ x₂) (β : y₁ ≅ y₂) {f : x₁ ⟶ y₁} {g : x₂ ⟶ y₂}
    (h : f = α.hom ≫ g ≫ β.inv) :
    α.inv ≫ f ≫ β.hom = g := by
  rw [h]
  simp [Category.assoc]

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n)) (k : ℕᵒᵖ)

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

variable [HasDerivedCategory.{wC} (EquivariantDiagram (harrisCongruenceGroups ρ p U m) (ModuleCat.{u}
    (HarrisCoefficientIntegers L p)))] [HasDerivedCategory.{wS} (Under k ⥤ (Sheaf
    (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} (HarrisCoefficientIntegers L p))))]

/-- Derive the source-local coefficient construction on the whole Harris
lattice diagram placed in degree q. -/
def harrisEtaleDerivedLocalCoefficient (q : ℤ) : DerivedCategory (Under k ⥤ (Sheaf
    (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} (HarrisCoefficientIntegers L p)))) :=
  (etaleAssociatedSourceDerivedFunctor X Y hY k).obj
    ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m))

/-- The same construction for the original coefficient reductions made
constant on the source torsor. -/
def harrisEtaleDerivedLocalConstant (q : ℤ) : DerivedCategory (Under k ⥤ (Sheaf
    (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u} (HarrisCoefficientIntegers L p)))) :=
  (etaleConstantSourceDerivedFunctor X Y k).obj
    ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m))

/-- Actual derived invariant evaluation for the full Harris coefficient
diagram through k. -/
def harrisEtaleDerivedLocalCoefficientIso (q : ℤ) :
    harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q ≅
      harrisEtaleDerivedLocalConstant ρ p U m X Y k q :=
  (etaleAssociatedSourceDerivedTrivialization X Y hY k).app
    ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m))

/-- Canonical comparison with the ordinary local coefficient diagram placed
in the same single degree. -/
def harrisEtaleDerivedLocalCoefficientSingleIso (q : ℤ) :
    harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q ≅
      (DerivedCategory.singleFunctor (Under k ⥤ (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)))) q).obj
        (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k) :=
  ((etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategorySingleFunctor q).app
      (harrisCoefficientDiagram ρ p U m)

/-- The constant-source derived object likewise recovers the ordinary
full-lattice constant diagram. -/
def harrisEtaleDerivedLocalConstantSingleIso (q : ℤ) :
    harrisEtaleDerivedLocalConstant ρ p U m X Y k q ≅
      (DerivedCategory.singleFunctor (Under k ⥤ (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)))) q).obj
        (harrisEtaleLocalConstantSystem ρ p U m X Y k) :=
  ((etaleConstantSourceSystemFunctor X Y k).mapDerivedCategorySingleFunctor q).app
      (harrisCoefficientDiagram ρ p U m)

/-- Conjugating by the canonical single-degree comparisons gives exactly
the existing ordinary Harris diagram trivialization. -/
@[reassoc]
theorem harrisEtaleDerivedLocalCoefficientIso_single (q : ℤ) :
    (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY k q).inv ≫
        (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q).hom ≫
        (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y k q).hom =
      (DerivedCategory.singleFunctor (Under k ⥤ (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)))) q).map
        (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom := by
  exact isoConjugation
    (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY k q)
    (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y k q)
    (etaleAssociatedSourceDerivedTrivialization_hom_app_single X Y hY k
      (harrisCoefficientDiagram ρ p U m) q)

variable [HasDerivedCategory.{wT} (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u}
    (HarrisCoefficientIntegers L p)))]

/-- Evaluation of a reachable coefficient level on actual derived categories. -/
def harrisEtaleDerivedLocalEvaluation (i : Under k) :
    DerivedCategory (Under k ⥤ (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u}
        (HarrisCoefficientIntegers L p)))) ⥤ DerivedCategory (Sheaf (X.smallEtaleTopology.over
        (Y.obj.obj k)) (ModuleCat.{u} (HarrisCoefficientIntegers L p))) :=
  ((CategoryTheory.evaluation (Under k) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i).mapDerivedCategory

instance (i : Under k) :
    (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).CommShift ℤ := by
  dsimp [harrisEtaleDerivedLocalEvaluation]
  infer_instance

instance (i : Under k) :
    (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).IsTriangulated := by
  dsimp [harrisEtaleDerivedLocalEvaluation]
  infer_instance

/-- Evaluating the coefficient single-degree comparison and then commuting
evaluation with singleFunctor. -/
def harrisEtaleDerivedLocalCoefficientEvaluationIso (q : ℤ) (i : Under k) :
    (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).obj
        (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q) ≅
      (DerivedCategory.singleFunctor (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u}
          (HarrisCoefficientIntegers L p))) q).obj
        ((harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k).obj i) :=
  (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).mapIso
      (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY k q) ≪≫
    (((CategoryTheory.evaluation (Under k) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i).mapDerivedCategorySingleFunctor
        q).app
      (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k)

/-- The corresponding evaluated comparison for the original coefficient
reductions made constant on the source torsor. -/
def harrisEtaleDerivedLocalConstantEvaluationIso (q : ℤ) (i : Under k) :
    (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).obj
        (harrisEtaleDerivedLocalConstant ρ p U m X Y k q) ≅
      (DerivedCategory.singleFunctor (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u}
          (HarrisCoefficientIntegers L p))) q).obj
        ((harrisEtaleLocalConstantSystem ρ p U m X Y k).obj i) :=
  (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).mapIso
      (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y k q) ≪≫
    (((CategoryTheory.evaluation (Under k) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i).mapDerivedCategorySingleFunctor
        q).app
      (harrisEtaleLocalConstantSystem ρ p U m X Y k)

/-- Every derived level component recovers the original invariant-section
evaluation along the genuine map of torsor covers. -/
@[reassoc]
theorem harrisEtaleDerivedLocalCoefficientIso_evaluation (q : ℤ) (i : Under k) :
    (harrisEtaleDerivedLocalCoefficientEvaluationIso ρ p U m X Y hY k q i).inv ≫
        (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k i).map
          (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q).hom ≫
        (harrisEtaleDerivedLocalConstantEvaluationIso ρ p U m X Y k q i).hom =
      (DerivedCategory.singleFunctor (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u}
          (HarrisCoefficientIntegers L p))) q).map
        (etaleAssociatedEvaluationAlong X Y (harrisCoefficientDiagram ρ p U m) i.right (Y.obj.map
            i.hom)) := by
  let E := (CategoryTheory.evaluation (Under k) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i
  have h := congrArg (fun f => E.mapDerivedCategory.map f)
    (harrisEtaleDerivedLocalCoefficientIso_single ρ p U m X Y hY k q)
  simp only [harrisEtaleDerivedLocalCoefficientEvaluationIso,
    harrisEtaleDerivedLocalConstantEvaluationIso, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  change (E.mapDerivedCategorySingleFunctor q).inv.app _ ≫
    E.mapDerivedCategory.map _ ≫ E.mapDerivedCategory.map _ ≫
    E.mapDerivedCategory.map _ ≫ (E.mapDerivedCategorySingleFunctor q).hom.app _ = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, h]
  have hn := (E.mapDerivedCategorySingleFunctor q).hom.naturality
    (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom
  simpa [E] using congrArg
    (fun f => (E.mapDerivedCategorySingleFunctor q).inv.app _ ≫ f) hn

/-- At the identity level the recovered derived map is exactly the original
single-exponent Harris coefficient trivialization placed in degree q. -/
@[reassoc]
theorem harrisEtaleDerivedLocalCoefficientIso_identity (q : ℤ) :
    (harrisEtaleDerivedLocalCoefficientEvaluationIso ρ p U m X Y hY k q
        (Under.mk (𝟙 k))).inv ≫
      (harrisEtaleDerivedLocalEvaluation ρ p U m X Y k (Under.mk (𝟙 k))).map
        (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q).hom ≫
      (harrisEtaleDerivedLocalConstantEvaluationIso ρ p U m X Y k q
        (Under.mk (𝟙 k))).hom =
    (DerivedCategory.singleFunctor (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k)) (ModuleCat.{u}
        (HarrisCoefficientIntegers L p))) q).map
      (harrisEtaleCoefficientTrivialization ρ p U m X Y hY k).hom := by
  rw [harrisEtaleDerivedLocalCoefficientIso_evaluation]
  change (DerivedCategory.singleFunctor (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
      ((harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app
        (Under.mk (𝟙 k))) = _
  rw [harrisEtaleLocalCoefficientDiagramIso_identity_hom]

end Langlands.Shimura.Coefficients
