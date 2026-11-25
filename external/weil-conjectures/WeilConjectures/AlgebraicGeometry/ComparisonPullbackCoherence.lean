/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Coherent comparison of etale and pro-etale inverse images

Source: blueprint, chap-Proper-base-change, theorem-proper-base-change-classical-pro,
node proposition-comparison-etale-derived-category--5; Stacks Project, Tags 098T, 099R, 00WX and
0B65.

The auxiliary interfaces extend the existing Kan-extension constructions to sets as
well as abelian groups and finite fixed-ring modules. Every comparison is the mate
of the canonical base-change isomorphism on restriction functors. No arbitrary
isomorphism is selected.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology D]
variable [∀ X : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology X) D]

/-- The constructed etale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable abbrev etaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable abbrev etaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleComparisonPullback D f ⊣ Etale.lowerStar D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The identity comparison, adjoint to the canonical fibre-product identity.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def etaleComparisonId (X : Scheme.{u}) :
    etaleComparisonPullback D (𝟙 X) ≅ 𝟭 _ :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 X)).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback (𝟙 X)
  (conjugateIsoEquiv Adjunction.id (etaleComparisonAdjunction D (𝟙 X))).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @Etale ⊤ X) D X.smallEtaleTopology).symm

/-- The composition comparison, adjoint to associativity of chosen fibre products.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def etaleComparisonComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleComparisonPullback D (f ≫ g) ≅
      etaleComparisonPullback D g ⋙ etaleComparisonPullback D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Z.smallEtaleTopology Y.smallEtaleTopology := Etale.isContinuous_overPullback g
  have : (MorphismProperty.Over.pullback @Etale ⊤ (f ≫ g)).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback (f ≫ g)
  ((conjugateIsoEquiv (etaleComparisonAdjunction D (f ≫ g))
    ((etaleComparisonAdjunction D g).comp (etaleComparisonAdjunction D f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm D
        Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology).symm).symm

/-- The specified square identification: compose through the equal composite morphisms.
The chosen Cartesian identification supplies the commutativity equation.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def etaleComparisonSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    etaleComparisonPullback D g ⋙ etaleComparisonPullback D f' ≅
      etaleComparisonPullback D f ⋙ etaleComparisonPullback D g' :=
  (etaleComparisonComp D f' g).symm ≪≫
    eqToIso (congrArg (etaleComparisonPullback D) sq.w.symm) ≪≫
      etaleComparisonComp D g' f

/-- The constructed proEtale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable abbrev proEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable abbrev proEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The identity comparison, adjoint to the canonical fibre-product identity.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def proEtaleComparisonId (X : Scheme.{u}) :
    proEtaleComparisonPullback D (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (proEtaleComparisonAdjunction D (𝟙 X))).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) D (Scheme.ProEt.topology X)).symm

/-- The composition comparison, adjoint to associativity of chosen fibre products.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def proEtaleComparisonComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleComparisonPullback D (f ≫ g) ≅
      proEtaleComparisonPullback D g ⋙ proEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv (proEtaleComparisonAdjunction D (f ≫ g))
    ((proEtaleComparisonAdjunction D g).comp (proEtaleComparisonAdjunction D f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm D
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).symm).symm

/-- The specified square identification: compose through the equal composite morphisms.
The chosen Cartesian identification supplies the commutativity equation.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def proEtaleComparisonSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    proEtaleComparisonPullback D g ⋙ proEtaleComparisonPullback D f' ≅
      proEtaleComparisonPullback D f ⋙ proEtaleComparisonPullback D g' :=
  (proEtaleComparisonComp D f' g).symm ≪≫
    eqToIso (congrArg (proEtaleComparisonPullback D) sq.w.symm) ≪≫
      proEtaleComparisonComp D g' f

/-- The canonical inverse-image comparison, normalized as the conjugate of
`lowerStarCompComparisonLowerStarIso`, which evaluates on `W` as the identity on
sections over `W ×[Y] X`. This extends the inverse of
`comparisonUpperStarCompUpperStarIso` to set coefficients.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
noncomputable def comparisonCoefficientPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleComparisonPullback D f ⋙ comparisonCoefficientPullback D X ≅
      comparisonCoefficientPullback D Y ⋙ proEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv
    ((etaleComparisonAdjunction D f).comp (comparisonCoefficientAdjunction D X))
    ((comparisonCoefficientAdjunction D Y).comp (proEtaleComparisonAdjunction D f))).symm
      (lowerStarCompComparisonLowerStarIso f D).symm).symm

section CoherenceProof

section RestrictionProof

attribute [local implicit_reducible] MorphismProperty Scheme.Etale Scheme.ProEt
  Scheme.smallEtaleTopology Scheme.toProEt MorphismProperty.Over.pullback
  Functor.sheafPushforwardContinuous MorphismProperty.Comma.changeProp
  MorphismProperty.Over.mk Scheme.instCategoryEtale Scheme.instCategoryProEt

private local instance etale_cont {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f

private theorem comparison_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    conjugateIsoEquiv
      ((comparisonCoefficientAdjunction D Y).comp (proEtaleComparisonAdjunction D f))
      ((etaleComparisonAdjunction D f).comp (comparisonCoefficientAdjunction D X))
      (comparisonCoefficientPullbackIso D f) = lowerStarCompComparisonLowerStarIso f D := by
  unfold comparisonCoefficientPullbackIso
  rw [conjugateIsoEquiv_iso_symm]
  rw [Equiv.apply_symm_apply]
  rfl

omit [∀ X : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology X) D] in
private theorem etale_comp_conjugate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv
      ((etaleComparisonAdjunction D g).comp (etaleComparisonAdjunction D f))
      (etaleComparisonAdjunction D (f ≫ g)) (etaleComparisonComp D f g) =
      Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm D
        Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology := by
  unfold etaleComparisonComp
  rw [conjugateIsoEquiv_iso_symm]
  rw [Equiv.apply_symm_apply]
  rfl

omit [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology D] in
private theorem proetale_comp_conjugate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv
      ((proEtaleComparisonAdjunction D g).comp (proEtaleComparisonAdjunction D f))
      (proEtaleComparisonAdjunction D (f ≫ g)) (proEtaleComparisonComp D f g) =
      Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm D
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) := by
  unfold proEtaleComparisonComp
  rw [conjugateIsoEquiv_iso_symm]
  rw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (etaleComparisonComp D f g) (comparisonCoefficientPullback D X) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (etaleComparisonPullback D g)
        (comparisonCoefficientPullbackIso D f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (comparisonCoefficientPullbackIso D g)
        (proEtaleComparisonPullback D f) ≪≫ Functor.associator _ _ _ =
    comparisonCoefficientPullbackIso D (f ≫ g) ≪≫
      Functor.isoWhiskerLeft (comparisonCoefficientPullback D Z) (proEtaleComparisonComp D f g)
      := by
  apply (conjugateIsoEquiv
    ((comparisonCoefficientAdjunction D Z).comp
      ((proEtaleComparisonAdjunction D g).comp (proEtaleComparisonAdjunction D f)))
    ((etaleComparisonAdjunction D (f ≫ g)).comp
      (comparisonCoefficientAdjunction D X))).injective
  rw [conjugateIsoEquiv_trans _
      (((etaleComparisonAdjunction D g).comp (etaleComparisonAdjunction D f)).comp
        (comparisonCoefficientAdjunction D X)),
    conjugateIsoEquiv_trans _
      ((etaleComparisonAdjunction D g).comp
        ((etaleComparisonAdjunction D f).comp (comparisonCoefficientAdjunction D X))),
    conjugateIsoEquiv_trans _
      ((etaleComparisonAdjunction D g).comp
        ((comparisonCoefficientAdjunction D Y).comp (proEtaleComparisonAdjunction D f))),
    conjugateIsoEquiv_trans _
      (((etaleComparisonAdjunction D g).comp (comparisonCoefficientAdjunction D Y)).comp
        (proEtaleComparisonAdjunction D f)),
    conjugateIsoEquiv_trans _
      (((comparisonCoefficientAdjunction D Z).comp (proEtaleComparisonAdjunction D g)).comp
        (proEtaleComparisonAdjunction D f)),
    conjugateIsoEquiv_trans _
      ((comparisonCoefficientAdjunction D Z).comp (proEtaleComparisonAdjunction D (f ≫ g)))]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_associator, conjugateIsoEquiv_iso_symm, comparison_conjugate,
    etale_comp_conjugate]
  rw [comparison_conjugate, comparison_conjugate, proetale_comp_conjugate]
  ext G W
  dsimp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
    Etale.lowerStar]
  simp only [Functor.sheafPushforwardContinuous, Functor.comp_obj, ObjectProperty.lift_obj_obj,
    ObjectProperty.ι_obj, Functor.whiskeringLeft_obj_obj, Functor.op_obj, Iso.refl_symm,
    Functor.isoWhiskerLeft_trans, Iso.trans_assoc, Functor.isoWhiskerRight_trans,
    Iso.symm_inv, Iso.symm_hom, Iso.refl_trans, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.refl_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, ObjectProperty.lift_map,
    Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_id', Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, NatTrans.op_app,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Functor.op_map, Quiver.Hom.unop_op,
    Category.comp_id]
  change
    G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
      (𝟙 ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
        ((Scheme.toProEt Z).obj (unop W))))).op ≫
      G.obj.map (𝟙 ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
          ((Scheme.toProEt Z).obj (unop W))))).op ≫
      G.obj.map ((Scheme.toProEt X).map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) f g).hom.app (unop W))).op =
    G.obj.map ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) f g).hom.app
      ((Scheme.toProEt Z).obj (unop W))).op ≫
      G.obj.map (𝟙 ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (f ≫ g)).obj
        ((Scheme.toProEt Z).obj (unop W)))).op
  simp only [CategoryTheory.Functor.map_id, CategoryTheory.op_id,
    Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_id_iso (X : Scheme.{u}) :
    comparisonCoefficientPullbackIso D (𝟙 X) ≪≫
        Functor.isoWhiskerLeft (comparisonCoefficientPullback D X) (proEtaleComparisonId D X) ≪≫
        (comparisonCoefficientPullback D X).rightUnitor =
      Functor.isoWhiskerRight (etaleComparisonId D X) (comparisonCoefficientPullback D X) ≪≫
        (comparisonCoefficientPullback D X).leftUnitor := by
  apply (conjugateIsoEquiv (comparisonCoefficientAdjunction D X)
    ((etaleComparisonAdjunction D (𝟙 X)).comp (comparisonCoefficientAdjunction D X))).injective
  rw [conjugateIsoEquiv_trans _
      ((comparisonCoefficientAdjunction D X).comp (proEtaleComparisonAdjunction D (𝟙 X))),
    conjugateIsoEquiv_trans _ ((comparisonCoefficientAdjunction D X).comp Adjunction.id),
    conjugateIsoEquiv_trans _ (Adjunction.id.comp (comparisonCoefficientAdjunction D X))]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_rightUnitor]
  rw [comparison_conjugate]
  unfold etaleComparisonId proEtaleComparisonId
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext G W
  dsimp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
    Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
    Functor.sheafPushforwardContinuousId',
    Etale.lowerStar]
  simp only [Functor.sheafPushforwardContinuous, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, Functor.whiskeringLeft_obj_obj, Functor.op_obj, Iso.trans_symm,
    Iso.symm_mk, Functor.isoWhiskerRight_trans, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app,
    Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    ObjectProperty.lift_map, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskeringLeft_obj_map, NatTrans.id_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousId_inv_app_hom_app, NatTrans.op_app,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Category.comp_id,
    Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_hom, Functor.rightUnitor_inv_app,
    op_unop, Functor.op_map, Quiver.Hom.unop_op]
  change G.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app
      ((Scheme.toProEt X).obj (unop W))).op ≫
      G.obj.map (𝟙 ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝟙 X)).obj
        ((Scheme.toProEt X).obj (unop W)))).op =
    G.obj.map ((Scheme.toProEt X).map
      ((MorphismProperty.Over.pullbackId @Etale ⊤ X).hom.app (unop W))).op
  simp only [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem comparison_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology D) :
    (comparisonCoefficientPullback D X).map ((etaleComparisonComp D f g).hom.app F) ≫
        (comparisonCoefficientPullbackIso D f).hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f).map ((comparisonCoefficientPullbackIso D g).hom.app F) =
      (comparisonCoefficientPullbackIso D (f ≫ g)).hom.app F ≫
        (proEtaleComparisonComp D f g).hom.app ((comparisonCoefficientPullback D Z).obj F) := by
  set_option backward.isDefEq.respectTransparency false in
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using
    congrArg (fun e ↦ e.hom.app F) (comparison_comp_iso D f g)

private theorem comparison_id (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D) :
    (comparisonCoefficientPullbackIso D (𝟙 X)).hom.app F ≫
        (proEtaleComparisonId D X).hom.app ((comparisonCoefficientPullback D X).obj F) =
      (comparisonCoefficientPullback D X).map ((etaleComparisonId D X).hom.app F) := by
  set_option backward.isDefEq.respectTransparency false in
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Functor.id_obj, Category.comp_id] using
    congrArg (fun e ↦ e.hom.app F) (comparison_id_iso D X)

end RestrictionProof

private theorem iso_square_paste {C : Type*} [Category* C]
    {A B E T A' B' E' T' : C} (a : A ≅ B) (e : E ≅ T)
    (b : B ≅ T) (d : A ≅ E) (α : A ≅ A') (β : E ≅ E')
    (a' : A' ≅ B') (b' : B' ≅ T') (d' : A' ≅ E') (e' : E' ≅ T')
    (h₁ : a ≪≫ b = d ≪≫ e) (h₂ : a' ≪≫ b' = d' ≪≫ e')
    (ht : d ≪≫ β = α ≪≫ d') :
    b ≪≫ e.symm ≪≫ β ≪≫ e' = a.symm ≪≫ α ≪≫ a' ≪≫ b' := by
  have hb : b = a.symm ≪≫ d ≪≫ e := by
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using
      congrArg (fun t ↦ a.symm ≪≫ t) h₁
  rw [hb]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc d β e', ht]
  simp only [Iso.trans_assoc]
  rw [h₂]

private theorem whiskered_iso_square_paste
    {A B P R : Type*} [Category* A] [Category* B] [Category* P] [Category* R]
    {L L' M M' : A ⥤ B} {R₀ R₀' R₁ R₁' : P ⥤ R} (K : B ⥤ R) (J : A ⥤ P)
    (a : L ≅ M) (e : R₀ ≅ R₁) (b : M ⋙ K ≅ J ⋙ R₁) (d : L ⋙ K ≅ J ⋙ R₀)
    (α : L ≅ L') (β : R₀ ≅ R₀') (a' : L' ≅ M')
    (b' : M' ⋙ K ≅ J ⋙ R₁') (d' : L' ⋙ K ≅ J ⋙ R₀') (e' : R₀' ≅ R₁')
    (h₁ : Functor.isoWhiskerRight a K ≪≫ b = d ≪≫ Functor.isoWhiskerLeft J e)
    (h₂ : Functor.isoWhiskerRight a' K ≪≫ b' = d' ≪≫ Functor.isoWhiskerLeft J e')
    (ht : d ≪≫ Functor.isoWhiskerLeft J β = Functor.isoWhiskerRight α K ≪≫ d') :
    b ≪≫ Functor.isoWhiskerLeft J (e.symm ≪≫ β ≪≫ e') =
      Functor.isoWhiskerRight (a.symm ≪≫ α ≪≫ a') K ≪≫ b' := by
  simp only [Functor.isoWhiskerLeft_trans, Functor.isoWhiskerRight_trans,
    Iso.trans_assoc]
  exact iso_square_paste (Functor.isoWhiskerRight a K) (Functor.isoWhiskerLeft J e)
    b d (Functor.isoWhiskerRight α K) (Functor.isoWhiskerLeft J β)
    (Functor.isoWhiskerRight a' K) b' d' (Functor.isoWhiskerLeft J e') h₁ h₂ ht

private noncomputable def comparison_path_generic
    {A B C P Q R : Type*} [Category* A] [Category* B] [Category* C]
    [Category* P] [Category* Q] [Category* R]
    {L₁ : A ⥤ B} {L₂ : B ⥤ C} {K₀ : A ⥤ P} {K₁ : B ⥤ Q} {K₂ : C ⥤ R}
    {R₁ : P ⥤ Q} {R₂ : Q ⥤ R}
    (c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂) (c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁) :
    (L₁ ⋙ L₂) ⋙ K₂ ≅ K₀ ⋙ R₁ ⋙ R₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ c₂ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c₁ R₂ ≪≫
      Functor.associator _ _ _

/-- Data of two comparison paths and their square identifications.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof step 4. -/
structure ComparisonSquareData
    (A B B' C P Q Q' R : Type*) [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R] where
  L₁ : A ⥤ B
  L₂ : B ⥤ C
  L₁' : A ⥤ B'
  L₂' : B' ⥤ C
  K₀ : A ⥤ P
  K₁ : B ⥤ Q
  K₁' : B' ⥤ Q'
  K₂ : C ⥤ R
  R₁ : P ⥤ Q
  R₂ : Q ⥤ R
  R₁' : P ⥤ Q'
  R₂' : Q' ⥤ R
  c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂
  c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁
  c₂' : L₂' ⋙ K₂ ≅ K₁' ⋙ R₂'
  c₁' : L₁' ⋙ K₁' ≅ K₀ ⋙ R₁'
  se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂'
  sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂'

/-- The componentwise square equation for the supplied comparison data.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof step 4. -/
def ComparisonSquareComponent
    {A B B' C P Q Q' R : Type*} [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R]
    (s : ComparisonSquareData A B B' C P Q Q' R) (F : A) : Prop :=
  s.c₂.hom.app (s.L₁.obj F) ≫ s.R₂.map (s.c₁.hom.app F) ≫ s.sp.hom.app (s.K₀.obj F) =
    s.K₂.map (s.se.hom.app F) ≫ s.c₂'.hom.app (s.L₁'.obj F) ≫
      s.R₂'.map (s.c₁'.hom.app F)

private def comparison_square_iso_condition
    {A B B' C P Q Q' R : Type*} [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R]
    {L₁ : A ⥤ B} {L₂ : B ⥤ C} {L₁' : A ⥤ B'} {L₂' : B' ⥤ C}
    {K₀ : A ⥤ P} {K₁ : B ⥤ Q} {K₁' : B' ⥤ Q'} {K₂ : C ⥤ R}
    {R₁ : P ⥤ Q} {R₂ : Q ⥤ R} {R₁' : P ⥤ Q'} {R₂' : Q' ⥤ R}
    (c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂) (c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁)
    (c₂' : L₂' ⋙ K₂ ≅ K₁' ⋙ R₂') (c₁' : L₁' ⋙ K₁' ≅ K₀ ⋙ R₁')
    (se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂') (sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂') : Prop :=
  comparison_path_generic c₂ c₁ ≪≫ Functor.isoWhiskerLeft K₀ sp =
      Functor.isoWhiskerRight se K₂ ≪≫ comparison_path_generic c₂' c₁'

private theorem comparison_square_components
    {A B B' C P Q Q' R : Type*} [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R]
    {L₁ : A ⥤ B} {L₂ : B ⥤ C} {L₁' : A ⥤ B'} {L₂' : B' ⥤ C}
    {K₀ : A ⥤ P} {K₁ : B ⥤ Q} {K₁' : B' ⥤ Q'} {K₂ : C ⥤ R}
    {R₁ : P ⥤ Q} {R₂ : Q ⥤ R} {R₁' : P ⥤ Q'} {R₂' : Q' ⥤ R}
    (c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂) (c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁)
    (c₂' : L₂' ⋙ K₂ ≅ K₁' ⋙ R₂') (c₁' : L₁' ⋙ K₁' ≅ K₀ ⋙ R₁')
    (se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂') (sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂')
    (h : comparison_square_iso_condition c₂ c₁ c₂' c₁' se sp) (F : A) :
    c₂.hom.app (L₁.obj F) ≫ R₂.map (c₁.hom.app F) ≫ sp.hom.app (K₀.obj F) =
      K₂.map (se.hom.app F) ≫ c₂'.hom.app (L₁'.obj F) ≫ R₂'.map (c₁'.hom.app F) := by
  unfold comparison_square_iso_condition at h
  simpa only [comparison_path_generic, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun e ↦ e.hom.app F) h

private theorem comparison_square_components_bundled
    {A B B' C P Q Q' R : Type*} [Category* A] [Category* B] [Category* B']
    [Category* C] [Category* P] [Category* Q] [Category* Q'] [Category* R]
    (s : ComparisonSquareData A B B' C P Q Q' R)
    (h : comparison_square_iso_condition s.c₂ s.c₁ s.c₂' s.c₁' s.se s.sp) (F : A) :
    ComparisonSquareComponent s F := by
  unfold ComparisonSquareComponent
  exact comparison_square_components s.c₂ s.c₁ s.c₂' s.c₁' s.se s.sp h F

/-- The canonical data of the specified etale/pro-etale square. Its fields use exactly
`comparisonCoefficientPullbackIso`, `etaleComparisonSquare`, and `proEtaleComparisonSquare`.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof step 4. -/
noncomputable def comparisonSquareData {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare g' f' f g) :
    ComparisonSquareData
      (Sheaf Y.smallEtaleTopology D) (Sheaf Y'.smallEtaleTopology D)
      (Sheaf X.smallEtaleTopology D) (Sheaf X'.smallEtaleTopology D)
      (Sheaf (Scheme.ProEt.topology Y) D) (Sheaf (Scheme.ProEt.topology Y') D)
      (Sheaf (Scheme.ProEt.topology X) D) (Sheaf (Scheme.ProEt.topology X') D) where
  L₁ := etaleComparisonPullback D g
  L₂ := etaleComparisonPullback D f'
  L₁' := etaleComparisonPullback D f
  L₂' := etaleComparisonPullback D g'
  K₀ := comparisonCoefficientPullback D Y
  K₁ := comparisonCoefficientPullback D Y'
  K₁' := comparisonCoefficientPullback D X
  K₂ := comparisonCoefficientPullback D X'
  R₁ := proEtaleComparisonPullback D g
  R₂ := proEtaleComparisonPullback D f'
  R₁' := proEtaleComparisonPullback D f
  R₂' := proEtaleComparisonPullback D g'
  c₂ := comparisonCoefficientPullbackIso D f'
  c₁ := comparisonCoefficientPullbackIso D g
  c₂' := comparisonCoefficientPullbackIso D g'
  c₁' := comparisonCoefficientPullbackIso D f
  se := etaleComparisonSquare D sq
  sp := proEtaleComparisonSquare D sq

private theorem comparison_transport_iso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    comparisonCoefficientPullbackIso D f ≪≫
        Functor.isoWhiskerLeft (comparisonCoefficientPullback D Y)
          (eqToIso (congrArg (proEtaleComparisonPullback D) h)) =
      Functor.isoWhiskerRight (eqToIso (congrArg (etaleComparisonPullback D) h))
        (comparisonCoefficientPullback D X) ≪≫ comparisonCoefficientPullbackIso D g := by
  subst g
  simp

set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_square_iso {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare g' f' f g) :
    let s := comparisonSquareData D g' f' f g sq
    comparison_square_iso_condition s.c₂ s.c₁ s.c₂' s.c₁' s.se s.sp := by
  dsimp only [comparisonSquareData]
  unfold comparison_square_iso_condition
  have h₁ : Functor.isoWhiskerRight (etaleComparisonComp D f' g)
      (comparisonCoefficientPullback D X') ≪≫ (comparison_path_generic
      (L₁ := etaleComparisonPullback D g) (L₂ := etaleComparisonPullback D f')
      (K₀ := comparisonCoefficientPullback D Y)
      (K₁ := comparisonCoefficientPullback D Y')
      (K₂ := comparisonCoefficientPullback D X')
      (R₁ := proEtaleComparisonPullback D g) (R₂ := proEtaleComparisonPullback D f')
      (comparisonCoefficientPullbackIso D f') (comparisonCoefficientPullbackIso D g)) =
    comparisonCoefficientPullbackIso D (f' ≫ g) ≪≫
      Functor.isoWhiskerLeft (comparisonCoefficientPullback D Y)
        (proEtaleComparisonComp D f' g) := comparison_comp_iso D f' g
  have h₂ : Functor.isoWhiskerRight (etaleComparisonComp D g' f)
      (comparisonCoefficientPullback D X') ≪≫ (comparison_path_generic
      (L₁ := etaleComparisonPullback D f) (L₂ := etaleComparisonPullback D g')
      (K₀ := comparisonCoefficientPullback D Y)
      (K₁ := comparisonCoefficientPullback D X)
      (K₂ := comparisonCoefficientPullback D X')
      (R₁ := proEtaleComparisonPullback D f) (R₂ := proEtaleComparisonPullback D g')
      (comparisonCoefficientPullbackIso D g') (comparisonCoefficientPullbackIso D f)) =
    comparisonCoefficientPullbackIso D (g' ≫ f) ≪≫
      Functor.isoWhiskerLeft (comparisonCoefficientPullback D Y)
        (proEtaleComparisonComp D g' f) := comparison_comp_iso D g' f
  rw [etaleComparisonSquare, proEtaleComparisonSquare]
  exact whiskered_iso_square_paste (comparisonCoefficientPullback D X')
    (comparisonCoefficientPullback D Y)
    (etaleComparisonComp D f' g) (proEtaleComparisonComp D f' g)
    ((comparison_path_generic
      (L₁ := etaleComparisonPullback D g) (L₂ := etaleComparisonPullback D f')
      (K₀ := comparisonCoefficientPullback D Y)
      (K₁ := comparisonCoefficientPullback D Y')
      (K₂ := comparisonCoefficientPullback D X')
      (R₁ := proEtaleComparisonPullback D g) (R₂ := proEtaleComparisonPullback D f')
      (comparisonCoefficientPullbackIso D f') (comparisonCoefficientPullbackIso D g)))
    (comparisonCoefficientPullbackIso D (f' ≫ g))
    (eqToIso (congrArg (etaleComparisonPullback D) sq.w.symm))
    (eqToIso (congrArg (proEtaleComparisonPullback D) sq.w.symm))
    (etaleComparisonComp D g' f) ((comparison_path_generic
      (L₁ := etaleComparisonPullback D f) (L₂ := etaleComparisonPullback D g')
      (K₀ := comparisonCoefficientPullback D Y)
      (K₁ := comparisonCoefficientPullback D X)
      (K₂ := comparisonCoefficientPullback D X')
      (R₁ := proEtaleComparisonPullback D f) (R₂ := proEtaleComparisonPullback D g')
      (comparisonCoefficientPullbackIso D g') (comparisonCoefficientPullbackIso D f)))
    (comparisonCoefficientPullbackIso D (g' ≫ f)) (proEtaleComparisonComp D g' f)
    h₁ h₂ (comparison_transport_iso D sq.w.symm)

end CoherenceProof

/-- The identity, composition and chosen Cartesian-square equations for the
canonical comparison. Equations are componentwise on every sheaf, equivalently
equalities of natural transformations. The square is the specified one, including
its commutativity transport; it is not replaced by an arbitrary isomorphism.
Source: blueprint, proposition-comparison-etale-derived-category--5, proof steps 1--4;
Stacks, Tags 00WX and 0B65 . -/
def ComparisonPullbackCoherent : Prop :=
  (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D),
    (comparisonCoefficientPullbackIso D (𝟙 X)).hom.app F ≫
        (proEtaleComparisonId D X).hom.app ((comparisonCoefficientPullback D X).obj F) =
      (comparisonCoefficientPullback D X).map ((etaleComparisonId D X).hom.app F)) ∧
  (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf Z.smallEtaleTopology D),
    (comparisonCoefficientPullback D X).map ((etaleComparisonComp D f g).hom.app F) ≫
        (comparisonCoefficientPullbackIso D f).hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f).map ((comparisonCoefficientPullbackIso D g).hom.app F) =
      (comparisonCoefficientPullbackIso D (f ≫ g)).hom.app F ≫
        (proEtaleComparisonComp D f g).hom.app ((comparisonCoefficientPullback D Z).obj F)) ∧
  (∀ (X' X Y' Y : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : ChosenCartesianSquare g' f' f g)
      (F : Sheaf Y.smallEtaleTopology D),
    ComparisonSquareComponent (comparisonSquareData D g' f' f g sq) F)

private theorem comparison_coherent : ComparisonPullbackCoherent D :=
  ⟨comparison_id D, fun _ _ _ f g ↦ comparison_comp D f g,
    fun _ _ _ _ g' f' f g sq F ↦
      comparison_square_components_bundled (comparisonSquareData D g' f' f g sq)
        (comparison_square_iso D g' f' f g sq) F⟩

/-- The canonical isomorphism `ν_U^* u⁻¹ ≅ u⁻¹ ν_V^*` is coherent for sets, abelian
sheaves and sheaves of modules over every finite discrete ring.
Source: blueprint, chap-Proper-base-change, theorem-proper-base-change-classical-pro,
proposition-comparison-etale-derived-category--5; Stacks, Tags 098T, 099R and 0B65.

Proof: (1) the etale-to-pro-etale inclusion commutes with base change: both composites
have the same fibre products and arrows. Restriction of sheaves therefore gives
`lowerStarCompComparisonLowerStarIso`. Scalar actions are the same constant sections,
so this works in fixed-ring modules as well as sets and abelian groups.
(2) Compose the inverse-image and comparison adjunctions (`Adjunction.comp`), and
apply the unit-normalized conjugation bijection (`conjugateIsoEquiv` and
`unit_conjugateEquiv_symm`). This is exactly `comparisonCoefficientPullbackIso`.
(3) For identities the right-image map is the identity after the fibre-product identity.
For composites, both right-image paths restrict along the same associativity map
`(W ×[Z] Y) ×[Y] X ≅ W ×[Z] X`, preserving the two projections. The composite Hom
bijections thus coincide; their injectivity proves the identity and composite equations.
(4) For the chosen Cartesian square, expand each square identification through the
composition comparisons and the supplied commutativity equation. Both paths on sections
identify the iterated products with `W ×[Y] X'` preserving both projections. Thus the
right-image maps agree, and injectivity of the adjunction Hom bijections proves the
specified square equation. These arguments are the node's four proof steps and retain
all identity, arbitrary-composite and chosen-square cases. -/
theorem comparison_pullback_coherent :
    ComparisonPullbackCoherent (Type (u + 1)) ∧
      ComparisonPullbackCoherent AddCommGrpCat.{u + 1} ∧
      ∀ (Λ : Type (u + 1)) [Ring Λ],
        ComparisonPullbackCoherent (ModuleCat.{u + 1} Λ) := by
  exact ⟨comparison_coherent _, comparison_coherent _, fun Λ _ ↦
    comparison_coherent (ModuleCat.{u + 1} Λ)⟩

end ProEtale
end AlgebraicGeometry

