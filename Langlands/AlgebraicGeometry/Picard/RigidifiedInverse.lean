import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundleTensor
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws

/-! # Rigidifying a specified tensor inverse -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

variable {X : Scheme.{u}}

lemma tensorLeftUnitor_inv_naturality {M N : X.Modules} (f : M ⟶ N) :
    (tensorLeftUnitor M).inv ≫ tensorMap (𝟙 (structureSheaf X)) f =
      f ≫ (tensorLeftUnitor N).inv := by
  apply (cancel_mono (tensorLeftUnitor N).hom).1
  rw [Category.assoc, tensorLeftUnitor_naturality, ← Category.assoc]
  simp

lemma tensorRigidification_factor {M N : X.Modules}
    (α : structureSheaf X ⟶ M) (β : structureSheaf X ⟶ N) :
    (tensorLeftUnitor (structureSheaf X)).inv ≫ tensorMap α β =
      β ≫ (tensorLeftUnitor N).inv ≫ tensorMap α (𝟙 N) := by
  rw [← Category.assoc β, ← tensorLeftUnitor_inv_naturality β, Category.assoc,
    tensorMap_comp (𝟙 (structureSheaf X)) α β (𝟙 N)]
  simp

end Langlands.Scheme.Modules

namespace Langlands.SchemeModule.RigidifiedModule

open Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

/-- The trivialization of a specified tensor inverse forced by evaluation and the
rigidification of the first factor. -/
def inverseTrivialization (L : RigidifiedModule ε) (M : X.Modules)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.carrier M ≅ structureSheaf X) :
    (Scheme.Modules.pullback ε).obj M ≅ structureModule S := by
  letI := preservation ε
  exact (tensorLeftUnitor ((Scheme.Modules.pullback ε).obj M)).symm ≪≫
    (Langlands.Scheme.Modules.tensorFunctor S).mapIso
      (L.rigidification.prod (Iso.refl _)) ≪≫
    ((asIso (pullbackTensorComparison ε)).app (L.carrier, M)).symm ≪≫
    (Scheme.Modules.pullback ε).mapIso evaluation ≪≫ pullbackUnitIso ε

/-- Equip a specified underlying tensor inverse with its evaluation-induced
rigidification. -/
def rigidifyInverse (L : RigidifiedModule ε) (M : X.Modules)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.carrier M ≅ structureSheaf X) :
    RigidifiedModule ε where
  carrier := M
  rigidification := (inverseTrivialization preservation L M evaluation).symm

lemma inverseEvaluation_compatibility (L : RigidifiedModule ε) (M : X.Modules)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.carrier M ≅ structureSheaf X) :
    (tensorObj preservation L (rigidifyInverse preservation L M evaluation)).rigidification.hom ≫
        (Scheme.Modules.pullback ε).map evaluation.hom =
      (pullbackUnitIso ε).inv := by
  let := preservation ε
  let δ := inverseTrivialization preservation L M evaluation
  let c := (asIso (pullbackTensorComparison ε)).app (L.carrier, M)
  have h :
      (tensorObj preservation L (rigidifyInverse preservation L M evaluation)).rigidification.hom =
        δ.inv ≫ (tensorLeftUnitor ((Scheme.Modules.pullback ε).obj M)).inv ≫
          Langlands.Scheme.Modules.tensorMap L.rigidification.hom (𝟙 _) ≫ c.inv := by
    apply (cancel_mono c.hom).1
    change
      (tensorObj preservation L (rigidifyInverse preservation L M evaluation)).rigidification.hom ≫
          pullbackTensorComparisonApp ε L.carrier M = _
    erw [tensorObj_rigidification_comp preservation L
      (rigidifyInverse preservation L M evaluation)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact tensorRigidification_factor L.rigidification.hom δ.inv
  let unitIso : (Scheme.Modules.pullback ε).obj (structureSheaf X) ≅ structureModule S :=
    pullbackUnitIso ε
  change _ = unitIso.inv
  rw [h]
  apply unitIso.comp_hom_eq_id.mp
  have hδ : δ.hom =
      (tensorLeftUnitor ((Scheme.Modules.pullback ε).obj M)).inv ≫
        Langlands.Scheme.Modules.tensorMap L.rigidification.hom (𝟙 _) ≫
          c.inv ≫ (Scheme.Modules.pullback ε).map evaluation.hom ≫
            unitIso.hom := rfl
  have hcancel := δ.inv_hom_id
  rw [hδ] at hcancel
  have reassoc :
      (((δ.inv ≫ (tensorLeftUnitor ((Scheme.Modules.pullback ε).obj M)).inv ≫
        Langlands.Scheme.Modules.tensorMap L.rigidification.hom (𝟙 _)) ≫ c.inv) ≫
        (Scheme.Modules.pullback ε).map evaluation.hom) ≫ unitIso.hom =
      δ.inv ≫ (tensorLeftUnitor ((Scheme.Modules.pullback ε).obj M)).inv ≫
        Langlands.Scheme.Modules.tensorMap L.rigidification.hom (𝟙 _) ≫
          c.inv ≫ (Scheme.Modules.pullback ε).map evaluation.hom ≫ unitIso.hom := by
    simp only [Category.assoc]
  exact reassoc.trans hcancel

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} {ε : S ⟶ X}

/-- Rigidify a supplied ordinary inverse line bundle using its actual evaluation. -/
def rigidifyInverse (L : RigidifiedLineBundle ε) (M : LineBundle X)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.obj.carrier M.obj ≅ structureSheaf X) :
    RigidifiedLineBundle ε :=
  ⟨RigidifiedModule.rigidifyInverse preservation L.obj M.obj evaluation, M.property⟩

/-- The supplied evaluation becomes an isomorphism of rigidified line bundles. -/
def inverseEvaluationIso (L : RigidifiedLineBundle ε) (M : LineBundle X)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.obj.carrier M.obj ≅ structureSheaf X) :
    tensor preservation L (rigidifyInverse preservation L M evaluation) ≅ trivial ε :=
  isoMk evaluation (RigidifiedModule.inverseEvaluation_compatibility
    preservation L.obj M.obj evaluation)

/-- Forgetting the lifted evaluation recovers the specified module isomorphism. -/
lemma inverseEvaluationIso_forget (L : RigidifiedLineBundle ε) (M : LineBundle X)
    (evaluation : Langlands.Scheme.Modules.tensorObj L.obj.carrier M.obj ≅ structureSheaf X) :
    ((forgetToRigidified ε ⋙ RigidifiedModule.forget ε).mapIso
      (inverseEvaluationIso preservation L M evaluation)) = evaluation := rfl

variable (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- The supplied inverse, equipped with its constructed rigidification, is a right
tensor inverse of the original compatible-isomorphism class. -/
lemma classesTensor_rigidifyInverse {T : Over S} (L : relative f ε section_eq T)
    (M : LineBundle ((relativeSpace f).obj T))
    (evaluation : Langlands.Scheme.Modules.tensorObj L.obj.carrier M.obj ≅
      structureSheaf ((relativeSpace f).obj T)) :
    classesTensor preservation f ε section_eq T (classOf f ε section_eq L)
        (classOf f ε section_eq (rigidifyInverse preservation L M evaluation)) =
      classOf f ε section_eq (trivial ((relativeSection f ε section_eq).app T)) :=
  Quotient.sound ⟨inverseEvaluationIso preservation L M evaluation⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
