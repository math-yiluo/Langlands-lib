import Langlands.GroupScheme.Dynamic.ConjugationFixedAttracting
import Langlands.GroupScheme.AffineGmEquivariantSmooth
import Langlands.GroupScheme.SmoothActionAffineOrbitProof

/-! # Actions on actual cocharacter fixed and attracting schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SchemeAction

section Factor

variable {S : Scheme.{u}} {H K : GroupScheme S} {X Y : Over S}
  (a : SchemeAction H X) (i : K ⟶ H) (j : Y ⟶ X) [Mono j]
  (m : K.X ⊗ Y ⟶ Y) (hm : m ≫ j = (i.hom.hom ⊗ₘ j) ≫ a.hom)

include hm

omit [Mono j] in
/-- A factor of an action morphism has the expected formula after its inclusion. -/
theorem factor_act_comp {T : Over S} (h : T ⟶ K.X) (y : T ⟶ Y) :
    (lift h y ≫ m) ≫ j = a.act (h ≫ i.hom.hom) (y ≫ j) := by
  rw [Category.assoc, hm, ← Category.assoc, lift_map]
  rfl

/-- An action morphism that factors through a subscheme supplies its actual action. -/
@[instance_reducible] def actionOnFactor : SchemeAction K Y :=
  schemeActionOfPointLaws m
    (fun y => by
      apply (cancel_mono j).mp
      rw [factor_act_comp a i j m hm, MonObj.one_comp, a.act_one])
    (fun h h' y => by
      apply (cancel_mono j).mp
      rw [factor_act_comp a i j m hm, factor_act_comp a i j m hm,
        factor_act_comp a i j m hm, MonObj.mul_comp, a.act_mul])

/-- The factored action retains the original action on every relative test. -/
theorem actionOnFactor_act_comp {T : Over S} (h : T ⟶ K.X) (y : T ⟶ Y) :
    (actionOnFactor a i j m hm).act h y ≫ j =
      a.act (h ≫ i.hom.hom) (y ≫ j) :=
  factor_act_comp a i j m hm h y

end Factor

section Equivariance

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}
  (a : SchemeAction H X) (χ : (Gm S).toGrp ⟶ H)

/-- The supplied action restricted along the cocharacter, in the pointwise interface. -/
abbrev cocharacterAction : PointwiseSchemeAction (Gm S).toGrp X :=
  (a.restrict χ).toPointwiseSchemeAction

/-- Postcomposition with the action morphism acts on the two components of any point. -/
theorem comp_actionHom {T : Over S} (z : T ⟶ H.X ⊗ X) :
    z ≫ a.hom = a.act (z ≫ fst H.X X) (z ≫ snd H.X X) := by
  rw [act, lift_comp_fst_snd]

/-- The action morphism is equivariant for conjugation on the group and restriction on X. -/
theorem actionHom_cocharacter_equivariant :
    ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)).IsEquivariant
      (a.cocharacterAction χ) a.hom := by
  intro T t z
  rw [comp_actionHom, PointwiseSchemeAction.prod_act_fst,
    PointwiseSchemeAction.prod_act_snd]
  simp only [cocharacterAction, toPointwiseSchemeAction_act, restrict_act,
    Dynamic.conjugationAction, AutomorphicAction.toPointwiseSchemeAction_act,
    AutomorphicAction.conjugation_act]
  rw [comp_actionHom, ← a.act_mul, ← a.act_mul]
  congr 1
  group

/-- The actual action relation is equivariant for the same source and diagonal target actions. -/
theorem relation_cocharacter_equivariant :
    ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)).IsEquivariant
      ((a.cocharacterAction χ).prod (a.cocharacterAction χ))
      (lift a.hom (snd H.X X)) := by
  intro T t z
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, PointwiseSchemeAction.prod_act_fst]
    exact a.actionHom_cocharacter_equivariant χ T t z
  · simp only [Category.assoc, lift_snd, PointwiseSchemeAction.prod_act_snd]

end Equivariance

section Affine

open GmCoordinateAction Dynamic.Affine

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} {X : Over (Spec R)}
  [IsAffine H.X.left] [IsAffine X.left]
  (a : SchemeAction H X) (χ : (Gm (Spec R)).toGrp ⟶ H)

local instance : IsAffine (H.X ⊗ X).left := by
  change IsAffine (CategoryTheory.Limits.pullback H.X.hom X.hom)
  infer_instance

local instance : IsAffine (X ⊗ X).left := by
  change IsAffine (CategoryTheory.Limits.pullback X.hom X.hom)
  infer_instance

private theorem centralizer_fixedProd :
    ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)).IsFixed
      ((centralizerHom χ).hom.hom ⊗ₘ
        schemeActionFixedHom (a.cocharacterAction χ)) := by
  rw [PointwiseSchemeAction.prod_isFixed_iff]
  constructor
  · rw [tensorHom_fst]
    have h := (exists_centralizer_factor_iff_fixed χ (centralizerHom χ).hom.hom).mp
      ⟨𝟙 _, Category.id_comp _⟩
    intro V b t
    simpa only [Category.assoc] using h V (b ≫ fst _ _) t
  · rw [tensorHom_snd]
    intro V b t
    simpa only [Category.assoc] using
      schemeActionFixedHom_isFixed (a.cocharacterAction χ) V (b ≫ snd _ _) t

/-- The original action on the centralizer and fixed subscheme factors through the fixed locus. -/
def cocharacterFixedActionHom :
    (centralizerScheme χ).X ⊗ schemeActionFixedScheme (a.cocharacterAction χ) ⟶
      schemeActionFixedScheme (a.cocharacterAction χ) :=
  ((exists_schemeActionFixed_factor_iff_all (a.cocharacterAction χ) _).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isFixed _ _
      (a.actionHom_cocharacter_equivariant χ) (a.centralizer_fixedProd χ))).choose

@[reassoc] theorem cocharacterFixedActionHom_comp :
    a.cocharacterFixedActionHom χ ≫ schemeActionFixedHom (a.cocharacterAction χ) =
      ((centralizerHom χ).hom.hom ⊗ₘ
        schemeActionFixedHom (a.cocharacterAction χ)) ≫ a.hom :=
  ((exists_schemeActionFixed_factor_iff_all (a.cocharacterAction χ) _).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isFixed _ _
      (a.actionHom_cocharacter_equivariant χ) (a.centralizer_fixedProd χ))).choose_spec

/-- The existing dynamic centralizer acts on the actual fixed scheme. -/
@[instance_reducible] def cocharacterFixedAction :
    SchemeAction (centralizerScheme χ) (schemeActionFixedScheme (a.cocharacterAction χ)) :=
  actionOnFactor a (centralizerHom χ) (schemeActionFixedHom (a.cocharacterAction χ))
    (a.cocharacterFixedActionHom χ) (a.cocharacterFixedActionHom_comp χ)

@[simp] theorem cocharacterFixedAction_hom :
    (a.cocharacterFixedAction χ).hom = a.cocharacterFixedActionHom χ := rfl

/-- On every test, the fixed action is the supplied original action after the inclusions. -/
theorem cocharacterFixedAction_act_comp {T : Over (Spec R)}
    (h : T ⟶ (centralizerScheme χ).X)
    (x : T ⟶ schemeActionFixedScheme (a.cocharacterAction χ)) :
    (a.cocharacterFixedAction χ).act h x ≫ schemeActionFixedHom (a.cocharacterAction χ) =
      a.act (h ≫ (centralizerHom χ).hom.hom)
        (x ≫ schemeActionFixedHom (a.cocharacterAction χ)) :=
  actionOnFactor_act_comp _ _ _ _ _ h x

private theorem parabolic_attractingProd :
    ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)).IsAttracted
      ((parabolicHom χ).hom.hom ⊗ₘ
        schemeActionAttractingHom (a.cocharacterAction χ)) := by
  rw [PointwiseSchemeAction.prod_isAttracted_iff]
  constructor
  · rw [tensorHom_fst]
    exact PointwiseSchemeAction.IsAttracted.comp _
      ((exists_parabolic_factor_iff_attracted χ (parabolicHom χ).hom.hom).mp
        ⟨𝟙 _, Category.id_comp _⟩) (fst _ _)
  · rw [tensorHom_snd]
    exact PointwiseSchemeAction.IsAttracted.comp _
      (schemeActionAttractingHom_isAttracted (a.cocharacterAction χ)) (snd _ _)

/-- The original parabolic action factors through the actual attracting scheme. -/
def cocharacterAttractingActionHom :
    (parabolicScheme χ).X ⊗ schemeActionAttractingScheme (a.cocharacterAction χ) ⟶
      schemeActionAttractingScheme (a.cocharacterAction χ) :=
  ((exists_schemeActionAttracting_factor_iff_all (a.cocharacterAction χ) _).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isAttracted _ _
      (a.actionHom_cocharacter_equivariant χ) (a.parabolic_attractingProd χ))).choose

@[reassoc] theorem cocharacterAttractingActionHom_comp :
    a.cocharacterAttractingActionHom χ ≫ schemeActionAttractingHom (a.cocharacterAction χ) =
      ((parabolicHom χ).hom.hom ⊗ₘ
        schemeActionAttractingHom (a.cocharacterAction χ)) ≫ a.hom :=
  ((exists_schemeActionAttracting_factor_iff_all (a.cocharacterAction χ) _).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isAttracted _ _
      (a.actionHom_cocharacter_equivariant χ) (a.parabolic_attractingProd χ))).choose_spec

/-- The existing dynamic parabolic acts on the actual attracting scheme. -/
@[instance_reducible] def cocharacterAttractingAction :
    SchemeAction (parabolicScheme χ) (schemeActionAttractingScheme (a.cocharacterAction χ)) :=
  actionOnFactor a (parabolicHom χ) (schemeActionAttractingHom (a.cocharacterAction χ))
    (a.cocharacterAttractingActionHom χ) (a.cocharacterAttractingActionHom_comp χ)

@[simp] theorem cocharacterAttractingAction_hom :
    (a.cocharacterAttractingAction χ).hom = a.cocharacterAttractingActionHom χ := rfl

/-- On every test, the attracting action is the supplied original action after inclusions. -/
theorem cocharacterAttractingAction_act_comp {T : Over (Spec R)}
    (h : T ⟶ (parabolicScheme χ).X)
    (x : T ⟶ schemeActionAttractingScheme (a.cocharacterAction χ)) :
    (a.cocharacterAttractingAction χ).act h x ≫
        schemeActionAttractingHom (a.cocharacterAction χ) =
      a.act (h ≫ (parabolicHom χ).hom.hom)
        (x ≫ schemeActionAttractingHom (a.cocharacterAction χ)) :=
  actionOnFactor_act_comp _ _ _ _ _ h x

/-- The source of the fixed action relation is the fixed source of the original relation. -/
def cocharacterFixedRelationSourceIso :
    (centralizerScheme χ).X ⊗ schemeActionFixedScheme (a.cocharacterAction χ) ≅
      schemeActionFixedScheme
        ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)) :=
  ((conjugationFixedIso χ).symm ⊗ᵢ Iso.refl _) ≪≫
    (schemeActionFixedProdIso (Dynamic.conjugationAction χ) (a.cocharacterAction χ)).symm

@[reassoc] theorem cocharacterFixedRelationSourceIso_hom_comp :
    (a.cocharacterFixedRelationSourceIso χ).hom ≫ schemeActionFixedHom
        ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)) =
      (centralizerHom χ).hom.hom ⊗ₘ schemeActionFixedHom (a.cocharacterAction χ) := by
  change (((conjugationFixedIso χ).inv ⊗ₘ 𝟙 _) ≫
    (schemeActionFixedProdIso _ _).inv) ≫ _ = _
  rw [Category.assoc, ← schemeActionFixedProdIso_hom_comp,
    Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom]
  simp only [conjugationFixedIso, centralizerToFixed_comp, Category.id_comp]

/-- The fixed action relation is the induced map of the original actual action relation. -/
theorem cocharacterFixedAction_relation :
    lift (a.cocharacterFixedAction χ).hom
        (snd (centralizerScheme χ).X (schemeActionFixedScheme (a.cocharacterAction χ))) =
      (a.cocharacterFixedRelationSourceIso χ).hom ≫
        schemeActionFixedMap
          ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ))
          ((a.cocharacterAction χ).prod (a.cocharacterAction χ))
          (a.relation_cocharacter_equivariant χ) ≫
        (schemeActionFixedProdIso (a.cocharacterAction χ) (a.cocharacterAction χ)).hom := by
  have hcomp :
      ((a.cocharacterFixedRelationSourceIso χ).hom ≫
        schemeActionFixedMap _ _ (a.relation_cocharacter_equivariant χ) ≫
        (schemeActionFixedProdIso _ _).hom) ≫
          (schemeActionFixedHom (a.cocharacterAction χ) ⊗ₘ
            schemeActionFixedHom (a.cocharacterAction χ)) =
        ((centralizerHom χ).hom.hom ⊗ₘ
          schemeActionFixedHom (a.cocharacterAction χ)) ≫ lift a.hom (snd H.X X) := by
    rw [Category.assoc, Category.assoc, schemeActionFixedProdIso_hom_comp,
      schemeActionFixedMap_comp, cocharacterFixedRelationSourceIso_hom_comp_assoc]
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono (schemeActionFixedHom (a.cocharacterAction χ))).mp
    simpa only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc,
      cocharacterFixedAction_hom,
      cocharacterFixedActionHom_comp] using
        (congrArg (fun f => f ≫ fst X X) hcomp).symm
  · apply (cancel_mono (schemeActionFixedHom (a.cocharacterAction χ))).mp
    simpa only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc] using
      (congrArg (fun f => f ≫ snd X X) hcomp).symm

/-- The source of the attracting action relation is the attracting source of the old relation. -/
def cocharacterAttractingRelationSourceIso :
    (parabolicScheme χ).X ⊗ schemeActionAttractingScheme (a.cocharacterAction χ) ≅
      schemeActionAttractingScheme
        ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)) :=
  ((conjugationAttractingIso χ).symm ⊗ᵢ Iso.refl _) ≪≫
    (schemeActionAttractingProdIso
      (Dynamic.conjugationAction χ) (a.cocharacterAction χ)).symm

@[reassoc] theorem cocharacterAttractingRelationSourceIso_hom_comp :
    (a.cocharacterAttractingRelationSourceIso χ).hom ≫ schemeActionAttractingHom
        ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ)) =
      (parabolicHom χ).hom.hom ⊗ₘ schemeActionAttractingHom (a.cocharacterAction χ) := by
  change (((conjugationAttractingIso χ).inv ⊗ₘ 𝟙 _) ≫
    (schemeActionAttractingProdIso _ _).inv) ≫ _ = _
  rw [Category.assoc, ← schemeActionAttractingProdIso_hom_comp,
    Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom]
  simp only [conjugationAttractingIso, parabolicToAttracting_comp, Category.id_comp]

/-- The attracting action relation is the induced map of the original actual relation. -/
theorem cocharacterAttractingAction_relation :
    lift (a.cocharacterAttractingAction χ).hom
        (snd (parabolicScheme χ).X (schemeActionAttractingScheme (a.cocharacterAction χ))) =
      (a.cocharacterAttractingRelationSourceIso χ).hom ≫
        schemeActionAttractingMap
          ((Dynamic.conjugationAction χ).prod (a.cocharacterAction χ))
          ((a.cocharacterAction χ).prod (a.cocharacterAction χ))
          (a.relation_cocharacter_equivariant χ) ≫
        (schemeActionAttractingProdIso
          (a.cocharacterAction χ) (a.cocharacterAction χ)).hom := by
  have hcomp :
      ((a.cocharacterAttractingRelationSourceIso χ).hom ≫
        schemeActionAttractingMap _ _ (a.relation_cocharacter_equivariant χ) ≫
        (schemeActionAttractingProdIso _ _).hom) ≫
          (schemeActionAttractingHom (a.cocharacterAction χ) ⊗ₘ
            schemeActionAttractingHom (a.cocharacterAction χ)) =
        ((parabolicHom χ).hom.hom ⊗ₘ
          schemeActionAttractingHom (a.cocharacterAction χ)) ≫ lift a.hom (snd H.X X) := by
    rw [Category.assoc, Category.assoc, schemeActionAttractingProdIso_hom_comp,
      schemeActionAttractingMap_comp, cocharacterAttractingRelationSourceIso_hom_comp_assoc]
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono (schemeActionAttractingHom (a.cocharacterAction χ))).mp
    simpa only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc,
      cocharacterAttractingAction_hom,
      cocharacterAttractingActionHom_comp] using
        (congrArg (fun f => f ≫ fst X X) hcomp).symm
  · apply (cancel_mono (schemeActionAttractingHom (a.cocharacterAction χ))).mp
    simpa only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc] using
      (congrArg (fun f => f ≫ snd X X) hcomp).symm

section Smooth

variable [Smooth H.X.hom] [Smooth X.hom]

local instance : Smooth (H.X ⊗ X).hom := by
  change Smooth (CategoryTheory.Limits.pullback.fst H.X.hom X.hom ≫ H.X.hom)
  infer_instance

local instance : Smooth (X ⊗ X).hom := by
  change Smooth (CategoryTheory.Limits.pullback.fst X.hom X.hom ≫ X.hom)
  infer_instance

/-- Smoothness of the actual action relation passes to the centralizer action on fixed points. -/
theorem smooth_cocharacterFixedAction_relation
    (hrel : Smooth (lift a.hom (snd H.X X)).left) :
    Smooth (lift (a.cocharacterFixedAction χ).hom
      (snd (centralizerScheme χ).X (schemeActionFixedScheme (a.cocharacterAction χ)))).left := by
  have := smooth_schemeActionFixedMap _ _ (a.relation_cocharacter_equivariant χ)
    inferInstance inferInstance hrel
  let : IsIso (a.cocharacterFixedRelationSourceIso χ).hom.left :=
    ((Over.forget _).mapIso (a.cocharacterFixedRelationSourceIso χ)).isIso_hom
  let : IsIso (schemeActionFixedProdIso (a.cocharacterAction χ)
      (a.cocharacterAction χ)).hom.left :=
    ((Over.forget _).mapIso (schemeActionFixedProdIso
      (a.cocharacterAction χ) (a.cocharacterAction χ))).isIso_hom
  rw [a.cocharacterFixedAction_relation χ, Over.comp_left, Over.comp_left]
  infer_instance

/-- Smoothness of the actual action relation passes to the parabolic action on attraction. -/
theorem smooth_cocharacterAttractingAction_relation
    (hrel : Smooth (lift a.hom (snd H.X X)).left) :
    Smooth (lift (a.cocharacterAttractingAction χ).hom
      (snd (parabolicScheme χ).X (schemeActionAttractingScheme (a.cocharacterAction χ)))).left := by
  have := smooth_schemeActionAttractingMap _ _ (a.relation_cocharacter_equivariant χ)
    inferInstance inferInstance hrel
  let : IsIso (a.cocharacterAttractingRelationSourceIso χ).hom.left :=
    ((Over.forget _).mapIso (a.cocharacterAttractingRelationSourceIso χ)).isIso_hom
  let : IsIso (schemeActionAttractingProdIso (a.cocharacterAction χ)
      (a.cocharacterAction χ)).hom.left :=
    ((Over.forget _).mapIso (schemeActionAttractingProdIso
      (a.cocharacterAction χ) (a.cocharacterAction χ))).isIso_hom
  rw [a.cocharacterAttractingAction_relation χ, Over.comp_left, Over.comp_left]
  infer_instance

end Smooth

end Affine

end Langlands.GroupScheme.SchemeAction
