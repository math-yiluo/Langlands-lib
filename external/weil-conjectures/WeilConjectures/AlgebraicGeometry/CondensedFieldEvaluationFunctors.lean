/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Mathlib.Algebra.Category.ModuleCat.Basic

import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-! # Evaluation of condensed-field modules over one geometric point

Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Continuous coefficient of a regular endomorphism at a geometric point. -/
@[irreducible] noncomputable def condensedFieldPointCoefficient
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (f : Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω)))) : E :=
  ((((condensedFieldContinuousMapIso E (Spec (.of Ω))).inv.hom ≫ f.hom ≫
    (condensedFieldContinuousMapIso E (Spec (.of Ω))).hom.hom).hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))) (ULift.up 1)).down z

/-- The regular-module normalization of evaluation over a geometric point. -/
def CondensedFieldPointScalarProperty
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⥤
      ModuleCat.{u + 1} E) : Prop :=
  ∃ b : H.obj (Mod.regular
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω)))) ≃ₗ[E] E,
    ∀ f : Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⟶
        Mod.regular
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))),
      b (H.map f (b.symm 1)) =
        condensedFieldPointCoefficient E Ω z f

-- The upstream Functor.Monoidal.evaluation has these same identity comparisons, but its
-- GlobalSectionsMonoidal module conflicts with the finite-coefficient notation imports here.
private noncomputable instance evaluationMonoidal
    {C : Type*} [Category C] {D : Type*} [Category D] [MonoidalCategory D] (U : C) :
    ((evaluation C D).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

private noncomputable abbrev pointSections (Ω : Type u) [Field Ω] :=
  sheafToPresheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))

private noncomputable def pointConstants
    (E : Type u) [NormedField E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    ULift.{u + 1} E ≃+* ULift.{u + 1} C(Spec (.of Ω), E) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down z)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext y
    exact congrArg f.down (Subsingleton.elim z y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private lemma pointSectionsMonObj
    (Ω : Type u) [Field Ω]
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) RingCat.{u + 1}) :
    (pointSections Ω).monObjObj
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R) =
      AddCommGrpCat.ringMonObj
        (R.obj.obj (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))) := by
  apply MonObj.ext
  let : MonObj ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R).obj :=
      R.obj.monObjCompForget₂
  have h := congr_app (Sheaf.μ_comp_map_mul
    ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R))
        (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))
  change (𝟙 _ ≫ _) ≫ _ = _
  rw [Category.id_comp]
  exact h

private noncomputable abbrev pointContinuousObj
    (E : Type u) [NormedField E] (Ω : Type u) [Field Ω] :=
  (sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf (Spec (.of Ω)) E)

private noncomputable def pointConstantHom
    (E : Type u) [NormedField E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    AddCommGrpCat.of (ULift.{u + 1} E) ⟶ (pointSections Ω).obj (pointContinuousObj E Ω) :=
  (pointConstants E Ω z).toAddEquiv.toAddCommGrpIso.hom

private instance pointConstantHom_isMonHom
    (E : Type u) [NormedField E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsMonHom (pointConstantHom E Ω z) := by
  have h := pointSectionsMonObj Ω (continuousCoefficientRingSheaf (Spec (.of Ω)) E)
  change @IsMonHom _ _ _ _ _ _ ((pointSections Ω).monObjObj _) _
  rw [h]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (pointConstants E Ω z).toRingHom

private instance pointConstantHom_isIso
    (E : Type u) [NormedField E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsIso (pointConstantHom E Ω z) := by
  unfold pointConstantHom
  infer_instance

private noncomputable def pointScalarHom
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    AddCommGrpCat.of (ULift.{u + 1} E) ⟶ (pointSections Ω).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) :=
  pointConstantHom E Ω z ≫ (pointSections Ω).map
    (condensedFieldContinuousMapIso E (Spec (.of Ω))).inv.hom

private instance pointScalarHom_isMonHom
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsMonHom (pointScalarHom E Ω z) := by
  unfold pointScalarHom
  infer_instance

private instance pointScalarHom_isIso
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsIso (pointScalarHom E Ω z) := by
  unfold pointScalarHom
  infer_instance

private noncomputable abbrev pointInternalEvaluation
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :=
  (pointSections Ω).mapMod
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⋙
    Mod.comap (pointScalarHom E Ω z)

private noncomputable def pointEvaluation
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :=
  pointInternalEvaluation E Ω z ⋙ CategoryTheory.internalToModule (ULift.{u + 1} E) ⋙
    ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom

private instance pointEvaluation_additive
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    (pointEvaluation E Ω z).Additive := by
  have : (CategoryTheory.internalToModule (ULift.{u + 1} E)).Additive :=
    ⟨by intros; rfl⟩
  unfold pointEvaluation
  infer_instance

private instance pointEvaluation_preservesFiniteColimits
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω)) :
    PreservesFiniteColimits (pointEvaluation E Ω z) := by
  have : PreservesFiniteColimits (pointSections Ω) :=
    (geometric_field_proetale_evaluation_exact Ω).2.2.1
  unfold pointEvaluation
  infer_instance

private noncomputable def pointRegularIso
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    (pointInternalEvaluation E Ω z).obj
        (Mod.regular
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω)))) ≅
      Mod.regular (AddCommGrpCat.of (ULift.{u + 1} E)) := by
  let r := pointScalarHom E Ω z
  refine Mod.isoMk (asIso r).symm ?_
  change (r ▷ _ ≫ MonObj.mul) ≫ inv r = _ ◁ inv r ≫ MonObj.mul
  rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
    ← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight, Category.id_comp]

private noncomputable def liftedRegularCoordinates (E : Type u) [Ring E] :
    ((CategoryTheory.internalToModule (ULift.{u + 1} E) ⋙
        ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom).obj
      (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} E)))) ≃ₗ[E] E where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def pointCoordinates
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    (pointEvaluation E Ω z).obj
        (Mod.regular
          (condensedRingObj (Profinite.continuousCoefficientRingObj E)
            (Spec (.of Ω)))) ≃ₗ[E] E := by
  let G := CategoryTheory.internalToModule (ULift.{u + 1} E) ⋙
    ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom
  exact (G.mapIso (pointRegularIso E Ω z)).toLinearEquiv.trans (liftedRegularCoordinates E)

/-- Evaluation at the final object over one algebraically closed field.

Source: Bhatt--Scholze, Example 4.2.11; Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).

Proof in words. Apply final-object sections to the underlying abelian sheaf and its
internal action. Sections is lax monoidal: its tensorator sends a pair of sections to
its tensor section, so its image is an internal module over the ring of global sections.
The canonical continuous realization identifies this ring with ULift E: every continuous
function on the one-point spectrum is constant, and evaluation at z is its inverse.
Transport the action along this ring isomorphism and use the tensor universal property
for internal modules in abelian groups to obtain an ordinary E-module. The internal
linearity diagrams make all evaluated arrows E-linear; they are unchanged as additive
maps, hence this functor is additive. Over an algebraically closed field every covering
of the final object splits. Consequently abelian sections preserves finite colimits.
The forgetful functor from internal modules computes those colimits, and the ordinary
module forgetful functor reflects them; hence evaluation preserves finite colimits.
The regular module gives E with its usual action. Evaluate its endomorphism at 1 to
get the displayed normalization, since both coefficient identifications are the
specified continuous realization followed by evaluation at z. -/
theorem exists_condensedField_point_evaluation
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω)) :
    ∃ H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⥤
        ModuleCat.{u + 1} E,
      H.Additive ∧ PreservesFiniteColimits H ∧ CondensedFieldPointScalarProperty E Ω z H := by
  refine ⟨pointEvaluation E Ω z, inferInstance, inferInstance, pointCoordinates E Ω z, ?_⟩
  intro f
  change (inv (pointScalarHom E Ω z)
    (((pointSections Ω).map f.hom) ((pointScalarHom E Ω z) (ULift.up 1)))).down = _
  unfold pointScalarHom
  rw [IsIso.inv_comp, ← Functor.map_inv]
  have he : inv (condensedFieldContinuousMapIso E (Spec (.of Ω))).inv.hom =
      (condensedFieldContinuousMapIso E (Spec (.of Ω))).hom.hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    exact congrArg (fun g ↦ g.hom)
      (condensedFieldContinuousMapIso E (Spec (.of Ω))).inv_hom_id
  have hc : inv (pointConstantHom E Ω z) =
      AddCommGrpCat.ofHom (pointConstants E Ω z).symm.toAddMonoidHom := by
    apply IsIso.inv_eq_of_hom_inv_id
    ext a
    rfl
  rw [he, hc]
  unfold condensedFieldPointCoefficient
  rfl

/-- The continuous coefficient ring is commutative, sectionwise. -/
instance continuousCoefficientRingObj_isComm
    (E : Type u) [NormedField E] :
    IsCommMonObj (Profinite.continuousCoefficientRingObj E) :=
  Sheaf.isCommMonObj_sheafCompose_obj
    (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E)
    (by
      intro S a b
      apply ULift.ext
      change (a.down * b.down : C(S.unop, E)) = b.down * a.down
      exact mul_comm a.down b.down)

/-- Pull a module to a geometric point after canonical coefficient change. -/
@[irreducible] noncomputable def condensedFieldGeometricModulePullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
      ((upperStar AddCommGrpCat.{u + 1} p).obj (condensedRingObj Λ X)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T) :=
  Mod.comap (inv (condensedPullbackHom Λ p)) ⋙ CondensedRing.upperStar Λ a

instance condensedFieldGeometricModulePullback_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    (condensedFieldGeometricModulePullback Λ p a).Additive := by
  unfold condensedFieldGeometricModulePullback
  infer_instance

instance condensedFieldGeometricModulePullback_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    PreservesFiniteColimits (condensedFieldGeometricModulePullback Λ p a) := by
  unfold condensedFieldGeometricModulePullback
  infer_instance

/-- Pulling back from X and then to T agrees with pullback along the composite. -/
noncomputable def condensedFieldGeometricModulePullbackComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    (upperStar AddCommGrpCat.{u + 1} p).mapMod (condensedRingObj Λ X) ⋙
        condensedFieldGeometricModulePullback Λ p a ≅
      CondensedRing.upperStar Λ (a ≫ p) := by
  unfold condensedFieldGeometricModulePullback
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((upperStar AddCommGrpCat.{u + 1} p).mapMod (condensedRingObj Λ X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ p)).symm)
      (CondensedRing.upperStar Λ a) ≪≫
    (CondensedRing.upperStarComp Λ a p).symm

/-- The geometric module pullback carries the regular module to the regular module.
Its first factor is the canonical coefficient comparison; the second factor is the
regular-module comparison for coefficient module inverse image. -/
@[irreducible] noncomputable def condensedFieldGeometricRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    (condensedFieldGeometricModulePullback Λ p a).obj
        (Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj (condensedRingObj Λ X))) ≅
      Mod.regular (condensedRingObj Λ T) := by
  unfold condensedFieldGeometricModulePullback
  exact (CondensedRing.upperStar Λ a).mapIso
      (Mod.regularIsoOfIsIso (condensedPullbackHom Λ p)) ≪≫
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ a)).app
      (((upperStar AddCommGrpCat.{u + 1} a).mapMod (condensedRingObj Λ V)).obj
        (Mod.regular (condensedRingObj Λ V))) ≪≫
    Mod.regularIsoOfIsIso (condensedPullbackHom Λ a)

end AlgebraicGeometry.ProEtale
