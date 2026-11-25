/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix

import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback

/-! # Compatibility of regular coefficients with geometric pullback

Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable abbrev coeff (E : Type u) [NormedField E] (X : Scheme.{u}) :=
  condensedFieldContinuousCoefficientObj E X

-- Keep scalar evaluation folded while composing identities: reducing the concrete
-- realization and pullback morphisms here expands their underlying constructions.
@[irreducible] private noncomputable def coefficientValue
    (E : Type u) [NormedField E] (X : Scheme.{u}) (x : X)
    (g : coeff E X ⟶ coeff E X) : E :=
  condensedFieldContinuousCoefficientMap E X g x

private lemma coefficientValue_eq
    (E : Type u) [NormedField E] (X : Scheme.{u}) (x : X)
    (g : coeff E X ⟶ coeff E X) :
    coefficientValue E X x g =
      ((g.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down x := by
  unfold coefficientValue condensedFieldContinuousCoefficientMap
  rfl


@[irreducible] private noncomputable def ringScalar
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) (x : X)
    (g : condensedRingObj (condensedFieldCoefficientRingObj E) X ⟶
      condensedRingObj (condensedFieldCoefficientRingObj E) X) : E :=
  coefficientValue E X x ((condensedFieldContinuousMapIso E X).inv.hom ≫ g ≫
    (condensedFieldContinuousMapIso E X).hom.hom)

private noncomputable def continuousPush (E : Type u) [NormedField E]
    {T V : Scheme.{u}} (a : T ⟶ V) :
    coeff E V ⟶ (lowerStar AddCommGrpCat.{u + 1} a).obj (coeff E T) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up
            (s.down.comp (pullback.fst U.unop.hom a).base.hom)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro U W f
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       ext x
       have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).map f.unop).left ≫
           pullback.fst U.unop.hom a = pullback.fst W.unop.hom a ≫ f.unop.left := by
         simp [MorphismProperty.Over.pullback]
       exact congrArg s.down (congrArg (fun g : pullback W.unop.hom a ⟶ U.unop.left ↦
         g x) h.symm) }⟩

private lemma realization_adjoint (E : Type u) [NormedField E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u}) :
    ((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _)
        (condensedFieldContinuousMapIso E X).hom.hom = comparisonAdjoint X E := by
  apply Sheaf.hom_ext
  ext S s
  cases s with
  | up s => exact condensedFieldContinuousMapIso_test E X S.unop s

private theorem realization_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E] :
    condensedPushforwardHom (condensedFieldCoefficientRingObj E) f ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (condensedFieldContinuousMapIso E Y).hom.hom =
    (condensedFieldContinuousMapIso E X).hom.hom ≫ continuousPush E f := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  have hleft := CondensedRing.chartMate_homEquiv f (toSpecZ X) (toSpecZ Y)
    (comp_toSpecZ f) (pointUpperStar.obj (condensedFieldCoefficientRingObj E))
    (coeff E Y) (condensedFieldContinuousMapIso E Y).hom.hom
  rw [← condensedPullbackHom_eq (condensedFieldCoefficientRingObj E) f] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  rw [show adjX.homEquiv _ _ (condensedFieldContinuousMapIso E X).hom.hom =
    comparisonAdjoint X E from realization_adjoint E X]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [condensedPushforwardHom, Adjunction.unitAlgHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  have hY := realization_adjoint E Y
  simp only [Adjunction.comp_homEquiv] at hY
  erw [hY]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor AddCommGrpCat.{u + 1} (comp_toSpecZ f)).inv.app
    (coeff E Y)).hom.app (op (profiniteToProEt.obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection Y S.unop)))).down =
    (((continuousPush E f).hom.app (op ((profiniteToProEtOf X).obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection X S.unop)))).down
  rw [lowerStarFactor_inv_app_hom_app]
  change (s.down.comp (profiniteTestProjection Y S.unop)).comp
      (((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection X S.unop)).comp
      (pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) =
      pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ X) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

private theorem continuous_unit_scalar {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [NormedField E] (p : coeff E X ⟶ coeff E X)
    (q : coeff E Y ⟶ coeff E Y)
    (h : continuousPush E f ≫ (lowerStar AddCommGrpCat.{u + 1} f).map q =
      p ≫ continuousPush E f) (y : Y) :
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down (f y) := by
  let V : Y.ProEt := Scheme.ProEt.mk (pullback.snd (𝟙 X) f)
  let v : V ⟶ Scheme.ProEt.mk (𝟙 Y) := MorphismProperty.Over.homMk V.hom
  let w : Y ⟶ pullback (𝟙 X) f := pullback.lift f (𝟙 Y) (by simp)
  let z := w y
  have hs := congrArg (fun k ↦ ((k.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
    (ULift.up 1)).down z) h
  have hn := congrArg (fun k : AddCommGrpCat.of (ULift.{u + 1} C(Y, E)) ⟶
      AddCommGrpCat.of (ULift.{u + 1} C(V.left, E)) ↦ (k (ULift.up 1)).down z)
    (q.hom.naturality v.op)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app, AddCommGrpCat.comp_apply] at hs
  change ((q.hom.app (op V)) (ULift.up 1)).down z =
    ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down
      (pullback.fst (𝟙 X) f z) at hs
  change ((q.hom.app (op V)) (ULift.up 1)).down z =
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down (V.hom z) at hn
  have hw₁ : w ≫ pullback.fst (𝟙 X) f = f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ V.hom = 𝟙 Y := pullback.lift_snd _ _ _
  have hz₁ : pullback.fst (𝟙 X) f z = f y :=
    congrArg (fun h : Y ⟶ X ↦ h y) hw₁
  have hz₂ : V.hom z = y := congrArg (fun h : Y ⟶ Y ↦ h y) hw₂
  rw [hz₁] at hs
  rw [hz₂] at hn
  exact hn.symm.trans hs

private theorem continuous_unit_scalar_value {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [NormedField E] (p : coeff E X ⟶ coeff E X)
    (q : coeff E Y ⟶ coeff E Y)
    (h : continuousPush E f ≫ (lowerStar AddCommGrpCat.{u + 1} f).map q =
      p ≫ continuousPush E f) (y : Y) :
    coefficientValue E Y y q = coefficientValue E X (f y) p := by
  delta coefficientValue condensedFieldContinuousCoefficientMap
  exact continuous_unit_scalar f E p q h y

private theorem adjunction_conjugation
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B : D} (α : L.obj A ⟶ B) [IsIso α] (p : A ⟶ A) :
    p ≫ (adj.unit.app A ≫ R.map α) =
      (adj.unit.app A ≫ R.map α) ≫ R.map (inv α ≫ L.map p ≫ α) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, IsIso.hom_inv_id, R.map_id, Category.id_comp]
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_map, Category.assoc] using
    congrArg (fun h ↦ h ≫ R.map α) (adj.unit.naturality p)

private theorem scalar_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (p : condensedRingObj (condensedFieldCoefficientRingObj E) X ⟶
      condensedRingObj (condensedFieldCoefficientRingObj E) X) (y : Y) :
    ringScalar E Y y
      (inv (condensedPullbackHom (condensedFieldCoefficientRingObj E) f) ≫
        (upperStar AddCommGrpCat.{u + 1} f).map p ≫
          condensedPullbackHom (condensedFieldCoefficientRingObj E) f) =
      ringScalar E X (f y) p := by
  delta ringScalar
  apply continuous_unit_scalar_value f E
  have h := CondensedRing.conjugated_morphism_square
    (lowerStar AddCommGrpCat.{u + 1} f)
    (condensedFieldContinuousMapIso E X).hom.hom
    (condensedFieldContinuousMapIso E Y).hom.hom
    (condensedPushforwardHom (condensedFieldCoefficientRingObj E) f)
    (continuousPush E f) p _ (realization_naturality f E)
    (adjunction_conjugation (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
      (condensedPullbackHom (condensedFieldCoefficientRingObj E) f) p)
  have hX : inv (condensedFieldContinuousMapIso E X).hom.hom =
      (condensedFieldContinuousMapIso E X).inv.hom := by
    simpa only [IsIso.Iso.inv_hom, Mon.forget] using
      (Functor.map_inv (Mon.forget _) (condensedFieldContinuousMapIso E X).hom).symm
  have hY : inv (condensedFieldContinuousMapIso E Y).hom.hom =
      (condensedFieldContinuousMapIso E Y).inv.hom := by
    simpa only [IsIso.Iso.inv_hom, Mon.forget] using
      (Functor.map_inv (Mon.forget _) (condensedFieldContinuousMapIso E Y).hom).symm
  simpa only [hX, hY] using h

private lemma conjugacy_naturalIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) (L M : D ⥤ E) (e : L ≅ M)
    {A : C} {B : D} {T : E} (q : P.obj A ≅ B) (k : M.obj B ≅ T) (f : A ⟶ A) :
    (L.mapIso q ≪≫ e.app B ≪≫ k).inv ≫ (P ⋙ L).map f ≫
      (L.mapIso q ≪≫ e.app B ≪≫ k).hom =
        k.inv ≫ M.map (q.inv ≫ P.map f ≫ q.hom) ≫ k.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.comp_map, Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [← L.map_comp_assoc, ← L.map_comp_assoc, e.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma regular_conjugate
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V)
    (f : Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj (condensedRingObj Λ X)) ⟶
      Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj (condensedRingObj Λ X))) :
    ((condensedFieldGeometricRegularIso Λ p a).inv ≫
      (condensedFieldGeometricModulePullback Λ p a).map f ≫
      (condensedFieldGeometricRegularIso Λ p a).hom).hom =
    inv (condensedPullbackHom Λ a) ≫
      (upperStar AddCommGrpCat.{u + 1} a).map
        (inv (condensedPullbackHom Λ p) ≫ f.hom ≫ condensedPullbackHom Λ p) ≫
      condensedPullbackHom Λ a := by
  let q := Mod.regularIsoOfIsIso (condensedPullbackHom Λ p)
  let e := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ a)
  let g := q.inv ≫ (Mod.comap (inv (condensedPullbackHom Λ p))).map f ≫ q.hom
  have h :
      (condensedFieldGeometricRegularIso Λ p a).inv ≫
        (condensedFieldGeometricModulePullback Λ p a).map f ≫
        (condensedFieldGeometricRegularIso Λ p a).hom =
      (Mod.regularIsoOfIsIso (condensedPullbackHom Λ a)).inv ≫
        (Mod.comap (inv (condensedPullbackHom Λ a))).map
          (((upperStar AddCommGrpCat.{u + 1} a).mapMod (condensedRingObj Λ V)).map g) ≫
        (Mod.regularIsoOfIsIso (condensedPullbackHom Λ a)).hom := by
    have hh := conjugacy_naturalIso
      (Mod.comap (inv (condensedPullbackHom Λ p)))
      (CondensedRing.upperStar Λ a)
      ((upperStar AddCommGrpCat.{u + 1} a).mapMod (condensedRingObj Λ V) ⋙
        Mod.comap (asIso (condensedPullbackHom Λ a)).inv)
      (Functor.isoWhiskerLeft
        ((upperStar AddCommGrpCat.{u + 1} a).mapMod (condensedRingObj Λ V)) e)
      q (Mod.regularIsoOfIsIso (condensedPullbackHom Λ a)) f
    unfold condensedFieldGeometricRegularIso condensedFieldGeometricModulePullback
    dsimp only [id]
    simpa only [q, e, g, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Iso.app, Functor.whiskerLeft_app, condensedFieldGeometricModulePullback,
      Functor.comp_map, asIso_inv] using hh
  rw [h]
  simp [g, q]

private lemma conjugate_comp
    {C : Type*} [Category C] {A B D : C}
    (α : A ⟶ B) [IsIso α] (e : B ≅ D) (f : A ⟶ A) :
    inv (α ≫ e.hom) ≫ f ≫ (α ≫ e.hom) =
      e.inv ≫ (inv α ≫ f ≫ α) ≫ e.hom := by
  simp only [IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc]

private lemma realization_conjugate
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (p : V ⟶ X)
    (f : (upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
      (upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (condensedFieldCoefficientRingObj E) X)) :
    inv (condensedFieldPullbackRealization E p) ≫ f ≫
        condensedFieldPullbackRealization E p =
      (condensedFieldContinuousMapIso E V).inv.hom ≫
        (inv (condensedPullbackHom (condensedFieldCoefficientRingObj E) p) ≫ f ≫
          condensedPullbackHom (condensedFieldCoefficientRingObj E) p) ≫
        (condensedFieldContinuousMapIso E V).hom.hom := by
  simp only [condensedFieldPullbackRealization_eq]
  exact conjugate_comp (condensedPullbackHom (condensedFieldCoefficientRingObj E) p)
    ((Mon.forget _).mapIso (condensedFieldContinuousMapIso E V)) f

private lemma pointCoefficient_eq
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (g : Mod.regular
      (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω)))) :
    condensedFieldPointCoefficient E Ω z g = ringScalar E (Spec (.of Ω)) z g.hom := by
  delta condensedFieldPointCoefficient ringScalar coefficientValue
    condensedFieldContinuousCoefficientMap
  rfl

private lemma pointCoefficient_from_hom
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) {V : Scheme.{u}}
    (a : Spec (.of Ω) ⟶ V)
    (p : condensedRingObj (condensedFieldCoefficientRingObj E) V ⟶
      condensedRingObj (condensedFieldCoefficientRingObj E) V)
    (g : Mod.regular
      (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω))))
    (h : g.hom = inv (condensedPullbackHom (condensedFieldCoefficientRingObj E) a) ≫
      (upperStar AddCommGrpCat.{u + 1} a).map p ≫
        condensedPullbackHom (condensedFieldCoefficientRingObj E) a) :
    condensedFieldPointCoefficient E Ω z g = ringScalar E V (a z) p := by
  have hg := congrArg (ringScalar E (Spec (.of Ω)) z) h
  exact (pointCoefficient_eq E Ω z g).trans (hg.trans (scalar_naturality a E p z))

private lemma pullbackScalar_eq
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (p : V ⟶ X) (x : V)
    (f : (upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
      (upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (condensedFieldCoefficientRingObj E) X)) :
    coefficientValue E V x (inv (condensedFieldPullbackRealization E p) ≫ f ≫
      condensedFieldPullbackRealization E p) =
      ringScalar E V x
        (inv (condensedPullbackHom (condensedFieldCoefficientRingObj E) p) ≫ f ≫
          condensedPullbackHom (condensedFieldCoefficientRingObj E) p) := by
  delta ringScalar
  exact congrArg (coefficientValue E V x) (realization_conjugate E p f)

set_option backward.isDefEq.respectTransparency true in
private lemma geometric_scalar_value
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] {X V : Scheme.{u}}
    (p : V ⟶ X) (a : Spec (.of Ω) ⟶ V) (z : Spec (.of Ω))
    (f : Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X)) ⟶
      Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (condensedFieldCoefficientRingObj E) X))) :
    condensedFieldPointCoefficient E Ω z
      ((condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a).inv ≫
        (condensedFieldGeometricModulePullback
          (condensedFieldCoefficientRingObj E) p a).map f ≫
        (condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a).hom) =
      coefficientValue E V (a z)
        (inv (condensedFieldPullbackRealization E p) ≫ f.hom ≫
          condensedFieldPullbackRealization E p) := by
  have h := pointCoefficient_from_hom E Ω z a
    (inv (condensedPullbackHom (condensedFieldCoefficientRingObj E) p) ≫ f.hom ≫
      condensedPullbackHom (condensedFieldCoefficientRingObj E) p)
    ((condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a).inv ≫
      (condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) p a).map f ≫
      (condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a).hom)
    (regular_conjugate (condensedFieldCoefficientRingObj E) p a f)
  exact h.trans (pullbackScalar_eq E p (a z) f.hom).symm

/-- Compatibility of a regular endomorphism's coefficient with one geometric pullback.

Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).

Proof in words. The extension-of-scalars regular-module comparison and naturality
of restriction of scalars identify the underlying conjugate by the canonical regular
isomorphism as the coefficient pullback comparison conjugating inverse image of f.
The adjoint-test equation of continuous realization gives its naturality square for a:
transpose both sides through the scheme and point adjunctions, then use the canonical
pullback projections. Conjugate the square by the realization isomorphisms and apply
it to the constant section 1 on the terminal pro-etale object. Pullback of the terminal
object has a canonical section above Spec Ω. Naturality along its terminal projection
identifies evaluation at z with evaluation at a(z). Finally expand the scalar evaluation
and the composite realization for p. The private lemmas above prove these conjugation,
naturality, and evaluation identities with folded scalar values; the final expansion
must be checked without unfolding the inverse-image constructions. No algebraic closure
assumption is needed for this coefficient identity. -/
theorem condensedField_geometric_regular_coefficient
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] {X V : Scheme.{u}}
    (p : V ⟶ X) (a : Spec (.of Ω) ⟶ V) (z : Spec (.of Ω))
    (f : Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X)) ⟶
      Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (condensedFieldCoefficientRingObj E) X))) :
    condensedFieldPointCoefficient E Ω z
      ((condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a).inv ≫
        (condensedFieldGeometricModulePullback
          (condensedFieldCoefficientRingObj E) p a).map f ≫
        (condensedFieldGeometricRegularIso (condensedFieldCoefficientRingObj E) p a).hom) =
      condensedFieldContinuousCoefficientMap E V
        (inv (condensedFieldPullbackRealization E p) ≫ f.hom ≫
          condensedFieldPullbackRealization E p) (a z) := by
  simpa only [coefficientValue] using geometric_scalar_value E Ω p a z f

end AlgebraicGeometry.ProEtale
