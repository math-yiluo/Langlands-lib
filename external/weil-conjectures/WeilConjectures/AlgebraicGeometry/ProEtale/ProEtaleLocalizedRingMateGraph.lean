/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocalizedRingMateGraphEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocalizedRingMateGraphEvaluation

/-!
# Localized ring-sheaf mates evaluated on graphs: the main statement

The helpers only expand the maps in the statement. In particular the mate uses the
specified Kan-extension/sheafification adjunction, and both forgetful and integer-unit
comparisons use the coprojection-normalized restriction comparisons. The private unit
computations live in
`WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocalizedRingMateGraphEvaluation`.

## References

* Stacks Project, Sites and Sheaves, Tags 03CE, 00Y0, 00VE and 00WX
* Modules on Sites, Tag 03EL
* Stacks, Tags 00Y0, 0H7J and 03EL
* Stacks, Sites and Sheaves, Tags 00VE, 00WX, 03CE and 00Y0
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The mate `u_* β ∘ e_u` for the specified ring inverse-image adjunction. -/
noncomputable def proEtaleLocalizedRingMate {B : Scheme.{u}} (V : B.ProEt)
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S) :
    R ⟶ (proEtaleSheafDirectImage V.hom CommRingCat.{u + 1}).obj S :=
  (proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R ≫
    (proEtaleSheafDirectImage V.hom CommRingCat.{u + 1}).map β.hom

/-- The ring isomorphism `bar β: R|_V ≅ S` under the normalized restriction comparison. -/
noncomputable def proEtaleLocalizedRingIso {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S) :
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      V.hom V.prop).obj R ≅ S :=
  (c.sheafIso.app R).symm ≪≫ β

/-- The graph `(b, U → V)` in the localization/base-change adjunction. -/
noncomputable def proEtaleLocalizationGraph {B : Scheme.{u}} (V : B.ProEt)
    (U : V.left.ProEt) (T : B.ProEt)
    (b : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj U ⟶ T) :
    U ⟶ (proEtaleBaseChange V.hom).obj T :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial).homEquiv U T b

/-- The identity of the underlying scheme identifies the composite of `V/V` with `V/B`. -/
def proEtaleLocalizationIdentityIso {B : Scheme.{u}} (V : B.ProEt) :
    (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj
      (ProEt.mk (𝟙 V.left)) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl V.left) rfl

/-- The additive sheaf map from the integer sheaf determined by a global section `r`.
The constant-sheaf/evaluation adjunction sends it to `n ↦ n • r` at `B/B`. -/
noncomputable def proEtaleLocalizedSectionMap (B : Scheme.{u})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (r : R.obj.obj (op (ProEt.mk (𝟙 B)))) :
    (constantSheaf (ProEt.topology B) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (sheafCompose (ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R :=
  ((constantSheafAdj (ProEt.topology B) AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale B)).homEquiv _ _).symm
      (AddCommGrpCat.ofHom (uliftZMultiplesHom _ r))

/-- The canonical integer-unit isomorphism `Z_V ≅ u⁻¹ Z_B` in localization coordinates.
First commute restriction with sheafification, then invert the normalized comparison. -/
noncomputable def proEtaleLocalizedIntegerUnit {B : Scheme.{u}} (V : B.ProEt)
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1}) :
    (constantSheaf (ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology B) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  letI : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).IsContinuous
      (ProEt.topology V.left) (ProEt.topology B) :=
    ProEt.isContinuous_overMap (V := V.left) (U := B) V.prop
  letI : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).IsCocontinuous
      (ProEt.topology V.left) (ProEt.topology B) :=
    ProEt.isCocontinuous_overMap (V := V.left) (U := B) V.prop
  (Functor.pushforwardContinuousSheafificationCompatibility
    (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop) AddCommGrpCat.{u + 1}
      (ProEt.topology V.left) (ProEt.topology B)).app
        ((Functor.const B.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≪≫
    (cA.sheafIso.app _).symm

/-- The inverse-image/underlying-additive-sheaf comparison, through normalized restriction.
Both middle presheaves are literally `U ↦ R(U → V → B)` with their additive structure. -/
noncomputable def proEtaleLocalizedAbelianComparison {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).obj
        ((sheafCompose (ProEt.topology B)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R) ≅
      (sheafCompose (ProEt.topology V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          ((proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R) :=
  cA.sheafIso.app _ ≪≫
    (sheafCompose (ProEt.topology V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (c.sheafIso.app R).symm

/-- Pull back the integer-to-`R` map and compose with `β`, using the canonical unit. -/
noncomputable def proEtaleLocalizedPulledSection {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S)
    (r : R.obj.obj (op (ProEt.mk (𝟙 B)))) :
    (constantSheaf (ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (sheafCompose (ProEt.topology V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj S :=
  (proEtaleLocalizedIntegerUnit V cA).hom ≫
    (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).map
      (proEtaleLocalizedSectionMap B R r) ≫
    (proEtaleLocalizedAbelianComparison V c cA R).hom ≫
    (sheafCompose (ProEt.topology V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map β.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedConstantInverse {B : Scheme.{u}} (V : B.ProEt)
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology B) D]
    [HasWeakSheafify (ProEt.topology V.left) D]
    (c : ProEtaleObjectRestrictionComparison V D) (A : D)
    (e : (constantSheaf (ProEt.topology V.left) D).obj A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction D V.hom V.prop).obj
        ((constantSheaf (ProEt.topology B) D).obj A))
    (he : ∀ U : V.left.ProEt,
      (toSheafify (ProEt.topology V.left) ((Functor.const V.left.ProEtᵒᵖ).obj A)).app
          (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology B) ((Functor.const B.ProEtᵒᵖ).obj A)).app
          (op ((MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj U))) :
    e.hom ≫ c.sheafIso.inv.app _ ≫
      proEtaleConstantInverseImageMap (X := V.left) (Y := B) V.hom D A = 𝟙 _ := by
  have h : c.sheafIso.hom.app _ ≫ e.inv =
      proEtaleConstantInverseImageMap (X := V.left) (Y := B) V.hom D A := by
    apply ((proEtaleSheafAdjunction (X := V.left) (Y := B) V.hom D).homEquiv _ _).injective
    erw [Adjunction.homEquiv_unit]
    change _ = ((proEtaleSheafAdjunction (X := V.left) (Y := B) V.hom D).homEquiv _ _)
      (((proEtaleSheafAdjunction (X := V.left) (Y := B) V.hom D).homEquiv _ _).symm
        (proEtaleConstantDirectImageMap (X := V.left) (Y := B) V.hom D A))
    erw [Equiv.apply_symm_apply]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology B) _ _
      ((proEtaleSheafDirectImage (X := V.left) (Y := B) V.hom D).obj
        ((constantSheaf (ProEt.topology V.left) D).obj A)).property
    apply NatTrans.ext
    funext T
    dsimp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
    change (toSheafify (ProEt.topology B) ((Functor.const B.ProEtᵒᵖ).obj A)).app T ≫
      (((proEtaleSheafAdjunction (X := V.left) (Y := B) V.hom D).unit.app _).hom.app T ≫
        (c.sheafIso.hom.app _).hom.app
          ((proEtaleBaseChange V.hom).op.obj T) ≫
        e.inv.hom.app ((proEtaleBaseChange V.hom).op.obj T)) = _
    erw [← Category.assoc (((proEtaleSheafAdjunction (X := V.left) (Y := B)
      V.hom D).unit.app _).hom.app T)]
    erw [normalizedUnit]
    have hn := (toSheafify (ProEt.topology B)
      ((Functor.const B.ProEtᵒᵖ).obj A)).naturality
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
          V.hom V.prop trivial).counit.app T.unop).op
    dsimp only [Functor.const_obj_map] at hn
    erw [← Category.assoc, ← hn, Category.id_comp, ← he]
    have hi := congrArg (fun z ↦ z.hom.app ((proEtaleBaseChange V.hom).op.obj T))
      e.hom_inv_id
    dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hi
    erw [Category.assoc, hi, Category.comp_id]
    have hd := ((sheafificationAdjunction (ProEt.topology B) D).homEquiv
      ((Functor.const B.ProEtᵒᵖ).obj A)
      ((proEtaleSheafDirectImage (X := V.left) (Y := B) V.hom D).obj
        ((constantSheaf (ProEt.topology V.left) D).obj A))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange V.hom).op
        (toSheafify (ProEt.topology V.left) ((Functor.const V.left.ProEtᵒᵖ).obj A)))
    exact (congrArg (fun z ↦ z.app T) hd).symm
  erw [← h]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantSectionUnit {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (D : Type*) [Category* D] [HasWeakSheafify J D]
    {T : C} (hT : IsTerminal T) (A : D) (R : Sheaf J D)
    (f : A ⟶ R.obj.obj (op T)) (U : Cᵒᵖ) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U ≫
        (((constantSheafAdj J D hT).homEquiv A R).symm f).hom.app U =
      f ≫ R.obj.map (hT.from U.unop).op := by
  let g := ((constantPresheafAdj D hT).homEquiv A R.obj).symm f
  have h := ((sheafificationAdjunction J D).homEquiv _ R).apply_symm_apply g
  change toSheafify J ((Functor.const Cᵒᵖ).obj A) ≫
    (((sheafificationAdjunction J D).homEquiv _ R).symm g).hom = g at h
  have hU := congrArg (fun z ↦ z.app U) h
  dsimp only [NatTrans.comp_app] at hU
  have hg : g.app U = f ≫ R.obj.map (hT.from U.unop).op := by
    dsimp only [g]
    rw [Adjunction.homEquiv_counit]
    rfl
  rw [hg] at hU
  rw [constantSheafAdj, Adjunction.comp_homEquiv]
  exact hU

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified Kan unit is projection restriction, and its ring-isomorphism mate
is evaluated on any graph by ordinary restriction followed by `bar β`. At the diagonal
this is a ring isomorphism. Pullback of an arbitrary global section uses the canonical
integer-unit comparison, inverse to the specified constant-coefficient map.
-/
theorem proEtaleLocalizedRingMateGraphEvaluation {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S) :
    (∀ (T : B.ProEt) (a : R.obj.obj (op T)),
      (c.sheafIso.hom.app R).hom.app (op ((proEtaleBaseChange V.hom).obj T))
          (((proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R).hom.app
            (op T) a) =
        R.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
          V.hom V.prop trivial).counit.app T).op a) ∧
    (∀ (T : B.ProEt) (a : R.obj.obj (op T)),
      (proEtaleLocalizedRingMate V R S β).hom.app (op T) a =
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app
          (op ((proEtaleBaseChange V.hom).obj T))
            (R.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
              V.hom V.prop trivial).counit.app T).op a)) ∧
    (∀ (T : B.ProEt) (a : R.obj.obj (op T)) (U : V.left.ProEt)
      (b : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj U ⟶ T),
      S.obj.map (proEtaleLocalizationGraph V U T b).op
          ((proEtaleLocalizedRingMate V R S β).hom.app (op T) a) =
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app (op U) (R.obj.map b.op a)) ∧
    ((proEtaleLocalizedRingMate V R S β).hom.app (op V) ≫
        S.obj.map (proEtaleLocalizationGraph V (ProEt.mk (𝟙 V.left)) V
          (proEtaleLocalizationIdentityIso V).hom).op =
      R.obj.map (proEtaleLocalizationIdentityIso V).hom.op ≫
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app
          (op (ProEt.mk (𝟙 V.left)))) ∧
    IsIso ((proEtaleLocalizedRingMate V R S β).hom.app (op V) ≫
      S.obj.map (proEtaleLocalizationGraph V (ProEt.mk (𝟙 V.left)) V
        (proEtaleLocalizationIdentityIso V).hom).op) ∧
    ((proEtaleLocalizedIntegerUnit V cA).hom ≫
        proEtaleConstantInverseImageMap V.hom AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)) = 𝟙 _) ∧
    (∀ r : R.obj.obj (op (ProEt.mk (𝟙 B))),
      (proEtaleLocalizedPulledSection V c cA R S β r).hom.app
          (op (ProEt.mk (𝟙 V.left)))
            ((toSheafify (ProEt.topology V.left)
              ((Functor.const V.left.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                  (op (ProEt.mk (𝟙 V.left))) (ULift.up 1)) =
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app (op (ProEt.mk (𝟙 V.left)))
          (R.obj.map ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale B).from
            ((MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj
              (ProEt.mk (𝟙 V.left)))).op r)) := by
  let F := MorphismProperty.Over.map (f := V.hom) ⊤ V.prop
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial
  let e := proEtaleLocalizedRingIso V c R S β
  have hu (T : B.ProEt) := normalizedUnit V CommRingCat.{u + 1} c R T
  have hm (T : B.ProEt) :
      (proEtaleLocalizedRingMate V R S β).hom.app (op T) =
        R.obj.map (a.counit.app T).op ≫
          e.hom.hom.app (op ((proEtaleBaseChange V.hom).obj T)) := by
    let W := (proEtaleBaseChange V.hom).obj T
    have hi := congrArg (fun z ↦ z.hom.app (op W)) (c.sheafIso.hom_inv_id_app R)
    dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hi
    have hunit : ((proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R).hom.app
        (op T) = R.obj.map (a.counit.app T).op ≫ (c.sheafIso.inv.app R).hom.app (op W) := by
      calc
        _ = ((proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R).hom.app
            (op T) ≫ ((c.sheafIso.hom.app R).hom.app (op W) ≫
              (c.sheafIso.inv.app R).hom.app (op W)) := by erw [hi, Category.comp_id]
        _ = _ := by erw [← Category.assoc, hu]
    change ((proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R).hom.app
      (op T) ≫ β.hom.hom.app (op W) = _
    simp only [hunit, e, proEtaleLocalizedRingIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Category.assoc]
    rfl
  have hg (T : B.ProEt) (U : V.left.ProEt) (b : F.obj U ⟶ T) :
      (proEtaleLocalizedRingMate V R S β).hom.app (op T) ≫
          S.obj.map (proEtaleLocalizationGraph V U T b).op =
        R.obj.map b.op ≫ e.hom.hom.app (op U) := by
    erw [hm, Category.assoc, ← e.hom.hom.naturality]
    change R.obj.map (a.counit.app T).op ≫
      R.obj.map (F.map (proEtaleLocalizationGraph V U T b)).op ≫ _ = _
    erw [← R.obj.map_comp_assoc, ← op_comp]
    have hp : F.map (proEtaleLocalizationGraph V U T b) ≫ a.counit.app T = b := by
      change F.map (a.homEquiv U T b) ≫ a.counit.app T = b
      exact (a.homEquiv U T).symm_apply_apply b
    erw [hp]
  have hd := hg V (ProEt.mk (𝟙 V.left)) (proEtaleLocalizationIdentityIso V).hom
  refine ⟨?_, ?_, ?_, hd, ?_, ?_, ?_⟩
  · intro T t
    exact congrArg (fun f ↦ f t) (hu T)
  · intro T t
    exact congrArg (fun f ↦ f t) (hm T)
  · intro T t U b
    exact congrArg (fun f ↦ f t) (hg T U b)
  · erw [hd]
    infer_instance
  · let : F.IsContinuous (ProEt.topology V.left) (ProEt.topology B) :=
      ProEt.isContinuous_overMap V.prop
    let : F.IsCocontinuous (ProEt.topology V.left) (ProEt.topology B) :=
      ProEt.isCocontinuous_overMap V.prop
    let E := (F.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
      (ProEt.topology V.left) (ProEt.topology B)).app
        ((Functor.const B.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    apply normalizedConstantInverse V AddCommGrpCat.{u + 1} cA
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) E
    intro U
    exact congrArg (fun z ↦ z.app (op U))
      (F.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u + 1}
        (ProEt.topology V.left) (ProEt.topology B)
        ((Functor.const B.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
  · intro r
    let G := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
    let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
    let ZB := (constantSheaf (ProEt.topology B) AddCommGrpCat.{u + 1}).obj Z
    let RA := (sheafCompose (ProEt.topology B) G).obj R
    let z := proEtaleLocalizedSectionMap B R r
    let : F.IsContinuous (ProEt.topology V.left) (ProEt.topology B) :=
      ProEt.isContinuous_overMap V.prop
    let : F.IsCocontinuous (ProEt.topology V.left) (ProEt.topology B) :=
      ProEt.isCocontinuous_overMap V.prop
    let E := (F.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
      (ProEt.topology V.left) (ProEt.topology B)).app
        ((Functor.const B.ProEtᵒᵖ).obj Z)
    have hn : cA.sheafIso.inv.app ZB ≫
        (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).map z ≫
        cA.sheafIso.hom.app RA =
      (AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
        V.hom V.prop).map z := by
      erw [← Category.assoc, ← cA.sheafIso.inv.naturality, Category.assoc,
        cA.sheafIso.inv_hom_id_app, Category.comp_id]
    have hp : proEtaleLocalizedPulledSection V c cA R S β r =
        E.hom ≫ (AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
          V.hom V.prop).map z ≫ (sheafCompose (ProEt.topology V.left) G).map e.hom := by
      change E.hom ≫ cA.sheafIso.inv.app ZB ≫
        (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).map z ≫
        (cA.sheafIso.hom.app RA ≫
          (sheafCompose (ProEt.topology V.left) G).map (c.sheafIso.inv.app R)) ≫
        (sheafCompose (ProEt.topology V.left) G).map β.hom = _
      calc
        _ = E.hom ≫ (cA.sheafIso.inv.app ZB ≫
            (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).map z ≫
              cA.sheafIso.hom.app RA) ≫
            (sheafCompose (ProEt.topology V.left) G).map (c.sheafIso.inv.app R) ≫
            (sheafCompose (ProEt.topology V.left) G).map β.hom := by
              simp only [Category.assoc]
        _ = _ := by
          rw [hn]
          simp only [e, proEtaleLocalizedRingIso, Iso.trans_hom, Iso.symm_hom,
            Iso.app_inv, Functor.map_comp]
    let U := ProEt.mk (𝟙 V.left)
    have hE : (toSheafify (ProEt.topology V.left)
        ((Functor.const V.left.ProEtᵒᵖ).obj Z)).app (op U) ≫ E.hom.hom.app (op U) =
      (toSheafify (ProEt.topology B) ((Functor.const B.ProEtᵒᵖ).obj Z)).app
        (op (F.obj U)) :=
      congrArg (fun t ↦ t.app (op U))
        (F.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u + 1}
          (ProEt.topology V.left) (ProEt.topology B)
          ((Functor.const B.ProEtᵒᵖ).obj Z))
    have hz := constantSectionUnit (ProEt.topology B) AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @WeaklyEtale B) Z RA
      (AddCommGrpCat.ofHom (uliftZMultiplesHom _ r)) (op (F.obj U))
    erw [hp]
    change e.hom.hom.app (op U) (z.hom.app (op (F.obj U))
      (E.hom.hom.app (op U) ((toSheafify (ProEt.topology V.left)
        ((Functor.const V.left.ProEtᵒᵖ).obj Z)).app (op U) (ULift.up 1)))) = _
    have he1 := congrArg (fun t ↦ t (ULift.up 1)) hE
    change E.hom.hom.app (op U) ((toSheafify (ProEt.topology V.left)
      ((Functor.const V.left.ProEtᵒᵖ).obj Z)).app (op U) (ULift.up 1)) = _ at he1
    erw [he1]
    have hz1 := congrArg (fun t ↦ t (ULift.up 1)) hz
    change z.hom.app (op (F.obj U)) ((toSheafify (ProEt.topology B)
      ((Functor.const B.ProEtᵒᵖ).obj Z)).app (op (F.obj U)) (ULift.up 1)) = _ at hz1
    erw [hz1]
    congr 1
    change R.obj.map ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale B).from
      (F.obj U)).op ((uliftZMultiplesHom _ r) (ULift.up 1)) = _
    simp only [uliftZMultiplesHom_apply_apply]
    change R.obj.map ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale B).from
      (F.obj U)).op ((1 : ℤ) • r) = _
    rw [one_zsmul]

end AlgebraicGeometry.Scheme
