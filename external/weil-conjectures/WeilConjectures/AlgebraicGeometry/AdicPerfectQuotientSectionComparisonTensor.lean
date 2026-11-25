/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionModel
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Tensor calculus for constant quotient sections

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK; Tag 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option linter.privateModule false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory.ConstantCompletion CategoryTheory.Functor
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change
  adicPerfectQuotientModuleStep
  AdicQuotientSections.rightAdjoint AdicQuotientSections.adjunction
  AdicQuotientSections.step AdicPerfectModel.constantPresentationIso

attribute [local implicit_reducible] sheafCompose Functor.sheafPushforwardContinuous

private def associatorWhisker {D E F G : Type*} [Category* D] [Category* E]
    [Category* F] [Category* G] {L : E ⥤ F} {K : F ⥤ G} {N : E ⥤ G}
    (P : D ⥤ E) (e : L ⋙ K ≅ N) : (P ⋙ L) ⋙ K ≅ P ⋙ N :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft P e

private theorem associatorWhisker_hom_app {D E F G : Type*} [Category* D] [Category* E]
    [Category* F] [Category* G] {L : E ⥤ F} {K : F ⥤ G} {N : E ⥤ G}
    (P : D ⥤ E) (e : L ⋙ K ≅ N) (M : D) :
    (associatorWhisker P e).hom.app M = e.hom.app (P.obj M) := by
  simp only [associatorWhisker, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]

attribute [irreducible] associatorWhisker

private def moduleValue {D : Type*} [Category* D] {A : Type w} [CommRing A]
    {F G : D ⥤ ModuleCat.{w} A} (α : F ⟶ G) (M : D) (x : F.obj M) : G.obj M :=
  (α.app M).hom x

private theorem moduleValue_ext {D : Type*} [Category* D] {A : Type w} [CommRing A]
    {F G : D ⥤ ModuleCat.{w} A} (α β : F ⟶ G)
    (h : ∀ (M : D) (x : F.obj M), moduleValue α M x = moduleValue β M x) : α = β := by
  ext M x
  exact h M x

private theorem moduleValue_comp {D : Type*} [Category* D] {A : Type w} [CommRing A]
    {F G H : D ⥤ ModuleCat.{w} A} (α : F ⟶ G) (β : G ⟶ H) (M : D) (x : F.obj M) :
    moduleValue (α ≫ β) M x = moduleValue β M (moduleValue α M x) := rfl

private theorem moduleValue_whiskerLeft {D E : Type*} [Category* D] [Category* E]
    {A : Type w} [CommRing A] (F : D ⥤ E) {G H : E ⥤ ModuleCat.{w} A}
    (α : G ⟶ H) (M : D) (x : (F ⋙ G).obj M) :
    moduleValue (whiskerLeft F α) M x = moduleValue α (F.obj M) x := rfl

attribute [irreducible] moduleValue

section SectionCarriers
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  {R S : Sheaf T CommRingCat.{w}}

private def natSection {D : Type*} [Category* D] {H K : D ⥤ Mod R}
    (f : H ⟶ K) (M : D) (V : Cᵒᵖ) (x : (H.obj M).val.obj V) :
    (K.obj M).val.obj V := ((f.app M).val.app V).hom x

private theorem natSection_inv_hom {D : Type*} [Category* D] {H K : D ⥤ Mod R}
    (e : H ≅ K) (M : D) (V : Cᵒᵖ) (x : (H.obj M).val.obj V) :
    natSection T e.inv M V (natSection T e.hom M V x) = x := by
  exact congrArg (fun f ↦ ((f.val.app V).hom x)) (e.hom_inv_id_app M)

private theorem natSection_comp {D : Type*} [Category* D] {F G H : D ⥤ Mod R}
    (α : F ⟶ G) (β : G ⟶ H) (M : D) (V : Cᵒᵖ) (x : (F.obj M).val.obj V) :
    natSection T (α ≫ β) M V x = natSection T β M V (natSection T α M V x) := rfl

private theorem natSection_whiskerLeft {D E : Type*} [Category* D] [Category* E]
    (F : D ⥤ E) {G H : E ⥤ Mod R} (α : G ⟶ H) (M : D) (V : Cᵒᵖ)
    (x : ((F ⋙ G).obj M).val.obj V) :
    natSection T (whiskerLeft F α) M V x = natSection T α (F.obj M) V x := rfl

attribute [irreducible] natSection

private def sectionRes (f : R ⟶ S) (M : Mod S) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((res f).obj M).val.obj V := x

private theorem sectionRes_eq (f : R ⟶ S) (M : Mod S) (V : Cᵒᵖ)
    (x : M.val.obj V) : sectionRes T f M V x = x := rfl

private def sectionOver (U : C) (M : Mod R) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op V.unop.left)) : (M.over U).val.obj V := x

private def sectionUnder (U : C) (M : Mod R) (V : (Over U)ᵒᵖ)
    (x : (M.over U).val.obj V) : M.val.obj (op V.unop.left) := x

private theorem sectionUnder_over (U : C) (M : Mod R) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op V.unop.left)) :
    sectionUnder T U M V (sectionOver T U M V x) = x := rfl

private theorem sectionOver_eq (U : C) (M : Mod R) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op V.unop.left)) : sectionOver T U M V x = x := rfl

attribute [irreducible] sectionRes sectionOver sectionUnder
end SectionCarriers

/-- The tensor/ideal-power quotient equivalence commutes with module maps.

Source: Stacks Project, Modules on Sites, section-tensor-product, Tag 03EK,
ordinary tensor functoriality; Mathlib's `TensorProduct.quotTensorEquivQuotSMul`.
Proof: use tensor induction. Zero and addition follow from linearity. For a pure
tensor, lift its quotient-ring scalar to an element `a` of `A`. The two images
are the quotient classes of `a • f x` and `f (a • x)`, equal by linearity of `f`.
This also covers exponent zero, zero modules, the zero ring, and either extreme
ideal, without extra hypotheses.
(auxiliary; not a blueprint node). -/
theorem adicPerfectTensorQuotient_naturality
    {A : Type w} [CommRing A] (I : Ideal A) (n : ℕ)
    {M N : ModuleCat.{w} A} (f : M ⟶ N)
    (x : (ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n))).obj M) :
    TensorProduct.quotTensorEquivQuotSMul N (I ^ n)
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n))).map f).hom x) =
      ((AdicCohomology.quotient I n).map f)
        (TensorProduct.quotTensorEquivQuotSMul M (I ^ n) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [_root_.map_add, hx, hy]
  | tmul a x =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change TensorProduct.quotTensorEquivQuotSMul N (I ^ n)
        (Ideal.Quotient.mk (I ^ n) a ⊗ₜ[A] f x) =
      ((AdicCohomology.quotient I n).map f)
        (TensorProduct.quotTensorEquivQuotSMul M (I ^ n)
          (Ideal.Quotient.mk (I ^ n) a ⊗ₜ[A] x))
    simp only [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    change Submodule.Quotient.mk (a • f x) = Submodule.Quotient.mk (f (a • x))
    rw [_root_.map_smul]

section AlgebraicQuotient
variable {A : Type w} [CommRing A] (I : Ideal A) (n : ℕ)

private def algebraicQuotientIso :
    ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)) ≅
        AdicCohomology.quotient I n := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let e := TensorProduct.quotTensorEquivQuotSMul M (I ^ n)
    let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n))).obj M)
    let e' : M' ≃ₗ[A] (AdicCohomology.quotient I n).obj M :=
      { e.toAddEquiv with
        map_smul' := by
          intro a z
          change e ((Ideal.Quotient.mk (I ^ n) a) • z) = a • e z
          exact (congrArg e (IsScalarTower.algebraMap_smul
            (M := TensorProduct A (A ⧸ I ^ n) M) (A ⧸ I ^ n) a z).symm).trans
              (e.map_smul a z) }
    exact e'.toModuleIso
  · intro M N f
    ext x
    exact adicPerfectTensorQuotient_naturality I n f x

private theorem algebraicQuotientIso_one (M : ModuleCat.{w} A) (x : M) :
    (algebraicQuotientIso I n).hom.app M
        ((1 : A ⧸ I ^ n) ⊗ₜ[A, Ideal.Quotient.mk (I ^ n)] x) =
      Submodule.Quotient.mk x :=
  TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (I ^ n) x

attribute [irreducible] algebraicQuotientIso

end AlgebraicQuotient

section ConstantScalar
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  {A B : Type w} [CommRing A] [CommRing B] (q : A →+* B)

private def constantTensorIso :
    commutativeSiteConstantModuleFunctor T A ⋙
        change ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom q)) ≅
      ModuleCat.extendScalars q ⋙ commutativeSiteConstantModuleFunctor T B := by
  have h (M : ModuleCat.{w} A) :
      IsIso (ConstantScalarRealization.moduleComparison T q M) :=
    (ConstantScalarRealization.moduleComparison_tensor T q M).1
  exact isoWhiskerLeft _ (AdicPerfectModel.constantChangeIso (J := T) q) ≪≫
    NatIso.ofComponents
      (fun M ↦ asIso (ConstantScalarRealization.moduleComparison T q M))
      (fun f ↦ ConstantScalarRealization.moduleComparison_naturality T q f)

private theorem constantTensorIso_one (M : ModuleCat.{w} A) (V : Cᵒᵖ) (x : M) :
    (((constantTensorIso T q).hom.app M).val.app V).hom
        (tensorSection ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom q))
          ((commutativeSiteConstantModuleFunctor T A).obj M) V 1
            (ConstantScalarRealization.constantSection T M V x)) =
      ConstantScalarRealization.constantSection T ((ModuleCat.extendScalars q).obj M) V
        ((1 : B) ⊗ₜ[A, q] x) := by
  let K := commutativeSiteConstantModuleFunctor T A
  have h := congrArg
    (fun f : K.obj M ⟶ (ConstantScalarRealization.restriction T q).obj
        ((ConstantScalarRealization.extension T q).obj (K.obj M)) ↦
      (f.val.app V).hom (ConstantScalarRealization.constantSection T M V x))
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (AdicPerfectModel.constantChangeAdjunction (J := T) q)
      (ConstantScalarRealization.adjunction T q) (K.obj M))
  change (((AdicPerfectModel.constantChangeIso (J := T) q).hom.app (K.obj M)).val.app V).hom
      (tensorSection ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom q))
        (K.obj M) V 1 (ConstantScalarRealization.constantSection T M V x)) =
    (((ConstantScalarRealization.adjunction T q).unit.app (K.obj M)).val.app V).hom
      (ConstantScalarRealization.constantSection T M V x) at h
  change ((ConstantScalarRealization.moduleComparison T q M).val.app V).hom
    ((((AdicPerfectModel.constantChangeIso (J := T) q).hom.app (K.obj M)).val.app V).hom _) = _
  rw [h]
  exact ConstantScalarRealization.moduleComparison_unit_section T q M V x

attribute [irreducible] constantTensorIso

private def constantQuotientIso (I : Ideal A) (n : ℕ) :
    commutativeSiteConstantModuleFunctor T A ⋙
        change ((constantSheaf T CommRingCat.{w}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) ⋙
        res ((constantSheaf T CommRingCat.{w}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) ≅
      AdicCohomology.quotient I n ⋙ commutativeSiteConstantModuleFunctor T A :=
  (Functor.associator _ _ _).symm ≪≫
  isoWhiskerRight (constantTensorIso T (Ideal.Quotient.mk (I ^ n))) _ ≪≫
    isoWhiskerLeft (ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n)))
      (ConstantScalarRealization.restrictionIso T (Ideal.Quotient.mk (I ^ n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (algebraicQuotientIso I n) _

private theorem constantQuotientIso_one (I : Ideal A) (n : ℕ)
    (M : ModuleCat.{w} A) (V : Cᵒᵖ) (x : M) :
    (((constantQuotientIso T I n).hom.app M).val.app V).hom
        (sectionRes T ((constantSheaf T CommRingCat.{w}).map
            (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))
          ((change ((constantSheaf T CommRingCat.{w}).map
            (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))).obj
              ((commutativeSiteConstantModuleFunctor T A).obj M)) V
          (tensorSection ((constantSheaf T CommRingCat.{w}).map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))
            ((commutativeSiteConstantModuleFunctor T A).obj M) V 1
              (ConstantScalarRealization.constantSection T M V x))) =
      ConstantScalarRealization.constantSection T ((AdicCohomology.quotient I n).obj M) V
        (Submodule.Quotient.mk x) := by
  unfold sectionRes
  let q := Ideal.Quotient.mk (I ^ n)
  let K := commutativeSiteConstantModuleFunctor T A
  change ((K.map ((algebraicQuotientIso I n).hom.app M)).val.app V).hom
    ((((ConstantScalarRealization.restrictionIso T q).hom.app
      ((ModuleCat.extendScalars q).obj M)).val.app V).hom
        ((((constantTensorIso T q).hom.app M).val.app V).hom
          (tensorSection ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom q))
            (K.obj M) V 1 (ConstantScalarRealization.constantSection T M V x)))) = _
  rw [constantTensorIso_one]
  have hr := (Classical.choose_spec
    (ConstantScalarRealization.restrictionIso_existsUnique T q)).1
      ((ModuleCat.extendScalars q).obj M) V ((1 : A ⧸ I ^ n) ⊗ₜ[A, q] x)
  change (((ConstantScalarRealization.restrictionIso T q).hom.app _).val.app V).hom
    (ConstantScalarRealization.constantSection T _ V _) = _ at hr
  rw [hr]
  refine (ConstantScalarRealization.constantSection_naturality T
    ((algebraicQuotientIso I n).hom.app M) V _).trans ?_
  exact congrArg
    (ConstantScalarRealization.constantSection T ((AdicCohomology.quotient I n).obj M) V)
    (algebraicQuotientIso_one I n M x)

attribute [irreducible] constantQuotientIso

end ConstantScalar

section SliceScalar
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  {R S B : Sheaf T CommRingCat.{w}} (φ : R ⟶ S) (π : S ⟶ B) (U : C)

private def canonicalChangeOver (f : R ⟶ S) :
    SheafOfModules.overFunctor _ U ⋙ change ((T.overPullback CommRingCat U).map f) ≅
      change f ⋙ SheafOfModules.overFunctor _ U :=
  NatIso.ofComponents (AdicPerfectModel.changeOverIso f U)
    (fun g ↦ AdicPerfectModel.changeOverIso_naturality f U g)

private theorem canonicalChangeOver_tensor (f : R ⟶ S) (M : Mod R)
    (V : (Over U)ᵒᵖ) (s : S.obj.obj (op V.unop.left))
    (x : M.val.obj (op V.unop.left)) :
    (((canonicalChangeOver T U f).hom.app M).val.app V).hom
        (tensorSection ((T.overPullback CommRingCat U).map f) (M.over U) V s x) =
      tensorSection f M (op V.unop.left) s x :=
  AdicPerfectModel.changeOverIso_tensor f U M V s x

attribute [irreducible] canonicalChangeOver

private def scalarSliceIso :
    change φ ⋙ SheafOfModules.overFunctor _ U ⋙
        change ((T.overPullback CommRingCat U).map π) ≅
      change (φ ≫ π) ⋙ SheafOfModules.overFunctor _ U :=
  isoWhiskerLeft (change φ) (canonicalChangeOver T U π) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (adicFiniteChangeComp φ π) (SheafOfModules.overFunctor _ U)

private theorem scalarSliceIso_one (M : Mod R) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op V.unop.left)) :
    (((scalarSliceIso T φ π U).hom.app M).val.app V).hom
        (tensorSection ((T.overPullback CommRingCat U).map π)
          (((change φ).obj M).over U) V 1
            (tensorSection φ M (op V.unop.left) 1 x)) =
      tensorSection (φ ≫ π) M (op V.unop.left) 1 x := by
  change (((adicFiniteChangeComp φ π).hom.app M).val.app (op V.unop.left)).hom
    ((((canonicalChangeOver T U π).hom.app ((change φ).obj M)).val.app V).hom _) = _
  rw [canonicalChangeOver_tensor]
  have h := (adicFiniteChangeComp_existsUnique φ π).exists.choose_spec
    M (op V.unop.left) 1 1 x
  simpa only [adicFiniteChangeComp, map_one, mul_one] using h

attribute [irreducible] scalarSliceIso

private def scalarSliceToIso (q : R ⟶ B) (h : φ ≫ π = q) :
    change φ ⋙ SheafOfModules.overFunctor _ U ⋙
        change ((T.overPullback CommRingCat U).map π) ≅
      change q ⋙ SheafOfModules.overFunctor _ U :=
  scalarSliceIso T φ π U ≪≫
    isoWhiskerRight (eqToIso (congrArg change h)) (SheafOfModules.overFunctor _ U)

private theorem scalarSliceToIso_one (q : R ⟶ B) (h : φ ≫ π = q)
    (M : Mod R) (V : (Over U)ᵒᵖ) (x : M.val.obj (op V.unop.left)) :
    (((scalarSliceToIso T φ π U q h).hom.app M).val.app V).hom
        (tensorSection ((T.overPullback CommRingCat U).map π)
          (((change φ).obj M).over U) V 1
            (tensorSection φ M (op V.unop.left) 1 x)) =
      tensorSection q M (op V.unop.left) 1 x := by
  subst q
  simpa only [scalarSliceToIso, eqToIso_refl, isoWhiskerRight_refl, Iso.trans_refl]
    using scalarSliceIso_one T φ π U M V x

attribute [irreducible] scalarSliceToIso

private def resOverIso (f : R ⟶ S) :
    SheafOfModules.overFunctor _ U ⋙ res ((T.overPullback CommRingCat U).map f) ≅
      res f ⋙ SheafOfModules.overFunctor _ U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def sliceQuotientIso {D : Type*} [Category* D] (q : R ⟶ S)
    {Q : D ⥤ D} {K : D ⥤ Mod R}
    {L : D ⥤ Mod (R.over U)} {F : D ⥤ Mod (S.over U)}
    (α : F ≅ K ⋙ change q ⋙ SheafOfModules.overFunctor _ U)
    (β : K ⋙ change q ⋙ res q ≅ Q ⋙ K)
    (l : L ≅ K ⋙ SheafOfModules.overFunctor _ U) :
    F ⋙ res ((T.overPullback CommRingCat U).map q) ≅ Q ⋙ L :=
  isoWhiskerRight α (res ((T.overPullback CommRingCat U).map q)) ≪≫
    isoWhiskerLeft (K ⋙ change q) (resOverIso T U q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight β (SheafOfModules.overFunctor _ U) ≪≫
    isoWhiskerLeft Q l.symm

private theorem sliceQuotientIso_apply {D : Type*} [Category* D] (q : R ⟶ S)
    {Q : D ⥤ D} {K : D ⥤ Mod R}
    {L : D ⥤ Mod (R.over U)} {F : D ⥤ Mod (S.over U)}
    (α : F ≅ K ⋙ change q ⋙ SheafOfModules.overFunctor _ U)
    (β : K ⋙ change q ⋙ res q ≅ Q ⋙ K)
    (l : L ≅ K ⋙ SheafOfModules.overFunctor _ U)
    (M : D) (V : (Over U)ᵒᵖ) (z : (F.obj M).val.obj V) :
    natSection (T.over U) (sliceQuotientIso T U q α β l).hom M V
        (sectionRes (T.over U) ((T.overPullback CommRingCat U).map q) (F.obj M) V z) =
      ((l.inv.app (Q.obj M)).val.app V).hom
        (sectionOver T U (K.obj (Q.obj M)) V
          (((β.hom.app M).val.app (op V.unop.left)).hom
            (sectionRes T q ((change q).obj (K.obj M)) (op V.unop.left)
              (sectionUnder T U ((change q).obj (K.obj M)) V
                (natSection (T.over U) α.hom M V z))))) := by
  unfold natSection sliceQuotientIso sectionOver sectionUnder sectionRes
  rfl

attribute [irreducible] sliceQuotientIso

private def localGenerator {A : Type w} [CommRing A] (M : ModuleCat.{w} A)
    (V : (Over U)ᵒᵖ) (x : M) :
    ((AdicQuotientSections.localConstant T A U).obj M).val.obj V :=
  (toSheafify (T.over U)
    ((siteConstantModulePresheafGeneral (C := Over U) A).obj M).presheaf).app V x

private theorem localConstantIso_generator {A : Type w} [CommRing A]
    (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    (((AdicQuotientSections.localConstantIso T A U).hom.app M).val.app V).hom
        (localGenerator T U M V x) =
      sectionOver T U ((commutativeSiteConstantModuleFunctor T A).obj M) V
        (ConstantScalarRealization.constantSection T M (op V.unop.left) x) := by
  unfold sectionOver
  have h := congrArg (fun f ↦ f.app V x)
    (AdicQuotientSections.localConstantMap_fac T A U M)
  exact h

private theorem localConstantIso_inv_generator {A : Type w} [CommRing A]
    (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    (((AdicQuotientSections.localConstantIso T A U).inv.app M).val.app V).hom
        (sectionOver T U ((commutativeSiteConstantModuleFunctor T A).obj M) V
          (ConstantScalarRealization.constantSection T M (op V.unop.left) x)) =
      localGenerator T U M V x := by
  rw [← localConstantIso_generator T U M V x]
  exact congrArg (fun f ↦ (f.val.app V).hom (localGenerator T U M V x))
    ((AdicQuotientSections.localConstantIso T A U).hom_inv_id_app M)

private theorem localGenerator_ext {A : Type w} [CommRing A]
    (M : ModuleCat.{w} A) {N : Mod ((constant T A).over U)}
    (f g : (AdicQuotientSections.localConstant T A U).obj M ⟶ N)
    (h : ∀ (V : (Over U)ᵒᵖ) (x : M),
      (f.val.app V).hom (localGenerator T U M V x) =
        (g.val.app V).hom (localGenerator T U M V x)) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (AdicQuotientSections.localRingUnit T A U)).injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def,
    PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  ext V x
  exact h V x

private theorem canonicalChangeOver_inv_tensor (f : R ⟶ S) (M : Mod R)
    (V : (Over U)ᵒᵖ) (s : S.obj.obj (op V.unop.left))
    (x : M.val.obj (op V.unop.left)) :
    (((canonicalChangeOver T U f).inv.app M).val.app V).hom
        (sectionOver T U ((change f).obj M) V
          (tensorSection f M (op V.unop.left) s x)) =
      tensorSection ((T.overPullback CommRingCat U).map f) (M.over U) V s
        (sectionOver T U M V x) := by
  unfold sectionOver
  rw [← canonicalChangeOver_tensor T U f M V s x]
  exact congrArg (fun k ↦ (k.val.app V).hom
    (tensorSection ((T.overPullback CommRingCat U).map f) (M.over U) V s x))
      ((canonicalChangeOver T U f).hom_inv_id_app M)

private theorem scalarCompTo_one (q : R ⟶ B) (h : φ ≫ π = q)
    (M : Mod R) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((((adicFiniteChangeComp φ π ≪≫ eqToIso (congrArg change h)).hom.app M).val.app V).hom)
        (tensorSection π ((change φ).obj M) V 1 (tensorSection φ M V 1 x)) =
      tensorSection q M V 1 x := by
  subst q
  have h := (adicFiniteChangeComp_existsUnique φ π).exists.choose_spec M V 1 1 x
  simpa only [adicFiniteChangeComp, eqToIso_refl, Iso.trans_refl, map_one, mul_one] using h

private def insertionStep (q : R ⟶ B) (h : φ ≫ π = q) :
    res φ ⟶ change π ⋙ res q :=
  (Functor.leftUnitor (res φ)).inv ≫
    whiskerRight (AdicPerfectModel.scalarAdjunction π).unit (res φ) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (change π) (ConstantCompletion.resCompIso φ π q h).hom

private theorem insertionStep_section (q : R ⟶ B) (h : φ ≫ π = q)
    (M : Mod S) (V : Cᵒᵖ) (x : M.val.obj V) :
    (((insertionStep T φ π q h).app M).val.app V).hom x = tensorSection π M V 1 x := by
  change (((ConstantCompletion.resCompIso φ π q h).hom.app ((change π).obj M)).val.app V).hom
    ((((AdicPerfectModel.scalarAdjunction π).unit.app M).val.app V).hom x) = _
  rw [ConstantCompletion.resCompIso_hom_apply]
  rfl

attribute [irreducible] insertionStep

private theorem localGenerator_naturality {A : Type w} [CommRing A]
    {M N : ModuleCat.{w} A} (f : M ⟶ N) (V : (Over U)ᵒᵖ) (x : M) :
    (((AdicQuotientSections.localConstant T A U).map f).val.app V).hom
        (localGenerator T U M V x) = localGenerator T U N V (f x) := by
  exact (congrArg (fun k ↦ k.app V x) (toSheafify_naturality (T.over U)
    ((Functor.const (Over U)ᵒᵖ).map ((forget₂ _ AddCommGrpCat).map f)))).symm

private theorem localNatural_ext {D : Type*} [Category* D]
    {A : Type w} [CommRing A] (P : D ⥤ ModuleCat.{w} A)
    {N : D ⥤ Mod ((constant T A).over U)}
    (α β : P ⋙ AdicQuotientSections.localConstant T A U ⟶ N)
    (h : ∀ (M : D) (V : (Over U)ᵒᵖ) (x : P.obj M),
      natSection (T.over U) α M V (localGenerator T U (P.obj M) V x) =
        natSection (T.over U) β M V (localGenerator T U (P.obj M) V x)) : α = β := by
  unfold natSection at h
  apply NatTrans.ext
  funext M
  apply localGenerator_ext T U (P.obj M)
  intro V x
  exact h M V x

private theorem localNatural_ext_surjective {D : Type*} [Category* D]
    {A : Type w} [CommRing A] (P : D ⥤ ModuleCat.{w} A) (Z : D → Type w)
    (p : ∀ M, Z M → P.obj M) (hp : ∀ M, Function.Surjective (p M))
    {N : D ⥤ Mod ((constant T A).over U)}
    (α β : P ⋙ AdicQuotientSections.localConstant T A U ⟶ N)
    (h : ∀ (M : D) (V : (Over U)ᵒᵖ) (x : Z M),
      natSection (T.over U) α M V (localGenerator T U (P.obj M) V (p M x)) =
        natSection (T.over U) β M V (localGenerator T U (P.obj M) V (p M x))) :
    α = β := by
  apply localNatural_ext T U P
  intro M V z
  obtain ⟨x, rfl⟩ := hp M z
  exact h M V x

private theorem localGenerator_nat {D : Type*} [Category* D]
    {A : Type w} [CommRing A] {P Q : D ⥤ ModuleCat.{w} A} (δ : P ⟶ Q)
    (M : D) (V : (Over U)ᵒᵖ) (x : P.obj M) :
    natSection (T.over U) (whiskerRight δ (AdicQuotientSections.localConstant T A U))
        M V (localGenerator T U (P.obj M) V x) =
      localGenerator T U (Q.obj M) V ((δ.app M).hom x) := by
  unfold natSection
  exact localGenerator_naturality T U (δ.app M) V x

private def directIso {D : Type*} [Category* D] {H K : D ⥤ Mod R} (e : H ≅ K)
    (q : R ⟶ B) (h : φ ≫ π = q) :
    (H ⋙ change φ ⋙ SheafOfModules.overFunctor _ U) ⋙
        change ((T.overPullback CommRingCat U).map π) ≅
      K ⋙ change q ⋙ SheafOfModules.overFunctor _ U :=
  isoWhiskerLeft H (scalarSliceToIso T φ π U q h) ≪≫
    isoWhiskerRight e (change q ⋙ SheafOfModules.overFunctor _ U)

private theorem directIso_hom_app {D : Type*} [Category* D] {H K : D ⥤ Mod R}
    (e : H ≅ K) (q : R ⟶ B) (h : φ ≫ π = q) (M : D) :
    (directIso T φ π U e q h).hom.app M =
      (scalarSliceToIso T φ π U q h).hom.app (H.obj M) ≫
        (((change q).map (e.hom.app M)).over U) := rfl

attribute [irreducible] directIso

private theorem directIso_one_base {D : Type*} [Category* D] {H K : D ⥤ Mod R} (e : H ≅ K)
    (q : R ⟶ B) (h : φ ≫ π = q) (M : D) (V : (Over U)ᵒᵖ)
    (x : (K.obj M).val.obj (op V.unop.left)) :
    (((directIso T φ π U e q h).hom.app M).val.app V).hom
        (tensorSection ((T.overPullback CommRingCat U).map π)
          (((change φ).obj (H.obj M)).over U) V 1
            (tensorSection φ (H.obj M) (op V.unop.left) 1
              (((e.inv.app M).val.app (op V.unop.left)).hom x))) =
      tensorSection q (K.obj M) (op V.unop.left) 1 x := by
  rw [directIso_hom_app]
  change ((((change q).map (e.hom.app M)).val.app (op V.unop.left)).hom)
    ((((scalarSliceToIso T φ π U q h).hom.app (H.obj M)).val.app V).hom
      (tensorSection ((T.overPullback CommRingCat U).map π)
        (((change φ).obj (H.obj M)).over U) V 1
          (tensorSection φ (H.obj M) (op V.unop.left) 1
            (((e.inv.app M).val.app (op V.unop.left)).hom x)))) = _
  rw [scalarSliceToIso_one, ConstantCompletion.tensorSection_map]
  have he := congrArg (fun f ↦ (f.val.app (op V.unop.left)).hom x) (e.inv_hom_id_app M)
  change ((e.hom.app M).val.app (op V.unop.left)).hom
    (((e.inv.app M).val.app (op V.unop.left)).hom x) = x at he
  rw [he]

private theorem directIso_one {D : Type*} [Category* D] {H K : D ⥤ Mod R} (e : H ≅ K)
    (q : R ⟶ B) (h : φ ≫ π = q) (M : D) (V : (Over U)ᵒᵖ)
    (x : (K.obj M).val.obj (op V.unop.left)) :
    (((directIso T φ π U e q h).hom.app M).val.app V).hom
        (tensorSection ((T.overPullback CommRingCat U).map π)
          (((change φ).obj (H.obj M)).over U) V 1
            (sectionOver T U ((change φ).obj (H.obj M)) V
              (tensorSection φ (H.obj M) (op V.unop.left) 1
                (((e.inv.app M).val.app (op V.unop.left)).hom x)))) =
      sectionOver T U ((change q).obj (K.obj M)) V
        (tensorSection q (K.obj M) (op V.unop.left) 1 x) := by
  rw [sectionOver_eq, sectionOver_eq]
  exact directIso_one_base T φ π U e q h M V x

private def presentationGenerator {D : Type*} [Category* D]
    {H K : D ⥤ Mod R} (e : H ≅ K) (M : D) (V : (Over U)ᵒᵖ)
    (x : (K.obj M).val.obj (op V.unop.left)) :
    (((change φ).obj (H.obj M)).over U).val.obj V :=
  sectionOver T U ((change φ).obj (H.obj M)) V
    (tensorSection φ (H.obj M) (op V.unop.left) 1
      (((e.inv.app M).val.app (op V.unop.left)).hom x))

private def directGenerator {D : Type*} [Category* D] (K : D ⥤ Mod R) (q : R ⟶ B)
    (M : D) (V : (Over U)ᵒᵖ) (x : (K.obj M).val.obj (op V.unop.left)) :
    (((change q).obj (K.obj M)).over U).val.obj V :=
  sectionOver T U ((change q).obj (K.obj M)) V
    (tensorSection q (K.obj M) (op V.unop.left) 1 x)

private theorem presentationGenerator_eq {D : Type*} [Category* D]
    {H K : D ⥤ Mod R} (e : H ≅ K) (M : D) (V : (Over U)ᵒᵖ)
    (x : (K.obj M).val.obj (op V.unop.left)) :
    presentationGenerator T φ U e M V x =
      sectionOver T U ((change φ).obj (H.obj M)) V
        (tensorSection φ (H.obj M) (op V.unop.left) 1
          (((e.inv.app M).val.app (op V.unop.left)).hom x)) := rfl

private theorem directGenerator_eq {D : Type*} [Category* D]
    (K : D ⥤ Mod R) (q : R ⟶ B) (M : D) (V : (Over U)ᵒᵖ)
    (x : (K.obj M).val.obj (op V.unop.left)) :
    directGenerator T U K q M V x =
      sectionOver T U ((change q).obj (K.obj M)) V
        (tensorSection q (K.obj M) (op V.unop.left) 1 x) := rfl

private theorem directIso_generator {D : Type*} [Category* D]
    {H K : D ⥤ Mod R} (e : H ≅ K) (q : R ⟶ B) (h : φ ≫ π = q)
    (M : D) (V : (Over U)ᵒᵖ) (x : (K.obj M).val.obj (op V.unop.left)) :
    natSection (T.over U) (directIso T φ π U e q h).hom M V
        (tensorSection ((T.overPullback CommRingCat U).map π)
          (((change φ).obj (H.obj M)).over U) V 1
            (presentationGenerator T φ U e M V x)) =
      directGenerator T U K q M V x := by
  unfold natSection
  rw [presentationGenerator_eq, directGenerator_eq]
  exact directIso_one T φ π U e q h M V x

attribute [irreducible] presentationGenerator directGenerator

private def sliceRealizationIso {D : Type*} [Category* D] (q : R ⟶ S)
    {K : D ⥤ Mod R} {L : D ⥤ Mod (R.over U)} {F : D ⥤ Mod (S.over U)}
    (α : F ≅ K ⋙ change q ⋙ SheafOfModules.overFunctor _ U)
    (l : L ≅ K ⋙ SheafOfModules.overFunctor _ U) :
    F ≅ L ⋙ change ((T.overPullback CommRingCat U).map q) :=
  α ≪≫ (isoWhiskerLeft K (canonicalChangeOver T U q)).symm ≪≫
    isoWhiskerRight l.symm (change ((T.overPullback CommRingCat U).map q))

private theorem sliceRealizationIso_generator {D : Type*} [Category* D] (q : R ⟶ S)
    {K : D ⥤ Mod R} {L : D ⥤ Mod (R.over U)} {F : D ⥤ Mod (S.over U)}
    (α : F ≅ K ⋙ change q ⋙ SheafOfModules.overFunctor _ U)
    (l : L ≅ K ⋙ SheafOfModules.overFunctor _ U) (M : D) (V : (Over U)ᵒᵖ)
    (x : (F.obj M).val.obj V) (k : (K.obj M).val.obj (op V.unop.left))
    (z : (L.obj M).val.obj V)
    (hα : (natSection (T.over U) α.hom M V x) =
      sectionOver T U ((change q).obj (K.obj M)) V
        (tensorSection q (K.obj M) (op V.unop.left) 1 k))
    (hl : (((l.inv.app M).val.app V).hom
      (sectionOver T U (K.obj M) V k)) = z) :
    natSection (T.over U) (sliceRealizationIso T U q α l).hom M V x =
      tensorSection ((T.overPullback CommRingCat U).map q) (L.obj M) V 1 z := by
  unfold natSection at hα ⊢
  unfold sliceRealizationIso
  change (((change ((T.overPullback CommRingCat U).map q)).map
      (l.inv.app M)).val.app V).hom
    ((((canonicalChangeOver T U q).inv.app (K.obj M)).val.app V).hom
      ((((α.hom.app M).val.app V).hom x))) = _
  rw [hα, canonicalChangeOver_inv_tensor]
  exact (ConstantCompletion.tensorSection_map ((T.overPullback CommRingCat U).map q)
    (M := (K.obj M).over U) (l.inv.app M) V 1 (sectionOver T U (K.obj M) V k)).trans
    (congrArg (tensorSection ((T.overPullback CommRingCat U).map q) (L.obj M) V 1) hl)

attribute [irreducible] sliceRealizationIso

private theorem insertionStep_section_res (q : R ⟶ B) (h : φ ≫ π = q)
    (M : Mod S) (V : Cᵒᵖ) (x : M.val.obj V) :
    natSection T (insertionStep T φ π q h) M V (sectionRes T φ M V x) =
      sectionRes T q ((change π).obj M) V (tensorSection π M V 1 x) := by
  unfold natSection
  rw [sectionRes_eq, sectionRes_eq]
  exact insertionStep_section T φ π q h M V x

private theorem res_natSection {D : Type*} [Category* D] (f : R ⟶ S)
    {H K : D ⥤ Mod S} (α : H ⟶ K) (M : D) (V : Cᵒᵖ)
    (x : (H.obj M).val.obj V) :
    natSection T (whiskerRight α (res f)) M V (sectionRes T f (H.obj M) V x) =
      sectionRes T f (K.obj M) V (natSection T α M V x) := by
  unfold natSection sectionRes
  rfl

private def functorScalarCompIso {D : Type*} [Category* D] (P : D ⥤ Mod R)
    (q : R ⟶ B) (h : φ ≫ π = q) :
    (P ⋙ change φ) ⋙ change π ≅ P ⋙ change q :=
  associatorWhisker P (adicFiniteChangeComp φ π ≪≫ eqToIso (congrArg change h))

private theorem functorScalarCompIso_hom_app {D : Type*} [Category* D]
    (P : D ⥤ Mod R) (q : R ⟶ B) (h : φ ≫ π = q) (M : D) :
    (functorScalarCompIso T φ π P q h).hom.app M =
      (adicFiniteChangeComp φ π ≪≫ eqToIso (congrArg change h)).hom.app (P.obj M) := by
  subst q
  unfold functorScalarCompIso
  simpa only [eqToIso_refl, Iso.trans_refl] using
    associatorWhisker_hom_app P (adicFiniteChangeComp φ π) M

private theorem functorScalarCompIso_one {D : Type*} [Category* D] (P : D ⥤ Mod R)
    (q : R ⟶ B) (h : φ ≫ π = q) (M : D) (V : Cᵒᵖ)
    (x : (P.obj M).val.obj V) :
    natSection T (functorScalarCompIso T φ π P q h).hom M V
        (tensorSection π ((P ⋙ change φ).obj M) V 1
          (tensorSection φ (P.obj M) V 1 x)) =
      tensorSection q (P.obj M) V 1 x := by
  subst q
  unfold natSection
  rw [functorScalarCompIso_hom_app]
  exact scalarCompTo_one T φ π (φ ≫ π) rfl (P.obj M) V x

attribute [irreducible] functorScalarCompIso

end SliceScalar

attribute [local irreducible] AdicQuotientSections.localConstantIso
  AdicQuotientSections.sectionsIso adicFiniteChangeComp

section ModelPresentation
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)

private theorem completionConeEq {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :
    coefficientMap T A J ≫ projection T A J n = ConstantCompletion.quotient T A J n :=
  limit.lift_π (quotientCone T A J) (op n)

private def modelPresentationFunctor (A : Type w) [CommRing A] :
    ModuleCat.{w} A ⥤ Mod (constant T A) :=
  SheafOfModules.strictPerfectConstantSheaf T A ⋙
    SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv

private def modelPresentationIso (A : Type w) [CommRing A] :
    modelPresentationFunctor T A ≅ commutativeSiteConstantModuleFunctor T A :=
  AdicPerfectModel.constantPresentationIso (J := T) (A := A)

attribute [irreducible] modelPresentationIso
private def rawModelGenerator {A : Type w} [CommRing A] (J : Ideal A) (U : C)
    (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    (((change (coefficientMap T A J)).obj
      ((modelPresentationFunctor T A).obj M)).over U).val.obj V :=
  presentationGenerator T (coefficientMap T A J) U (modelPresentationIso T A) M V
    (ConstantScalarRealization.constantSection T M (op V.unop.left) x)

private def rawDirectGenerator {A : Type w} [CommRing A] (J : Ideal A) (U : C)
    (n : ℕ) (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    (((change (ConstantCompletion.quotient T A J n)).obj
      ((commutativeSiteConstantModuleFunctor T A).obj M)).over U).val.obj V :=
  directGenerator T U (commutativeSiteConstantModuleFunctor T A)
    (ConstantCompletion.quotient T A J n) M V
    (ConstantScalarRealization.constantSection T M (op V.unop.left) x)

attribute [irreducible] rawModelGenerator rawDirectGenerator

private theorem rawModelGenerator_eq {A : Type w} [CommRing A] (J : Ideal A) (U : C)
    (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    rawModelGenerator T J U M V x =
      presentationGenerator T (coefficientMap T A J) U (modelPresentationIso T A) M V
        (ConstantScalarRealization.constantSection T M (op V.unop.left) x) := by
  unfold rawModelGenerator
  rfl

private theorem rawDirectGenerator_alias {A : Type w} [CommRing A] (J : Ideal A) (U : C)
    (n : ℕ) (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    rawDirectGenerator T J U n M V x =
      directGenerator T U (commutativeSiteConstantModuleFunctor T A)
        (ConstantCompletion.quotient T A J n) M V
        (ConstantScalarRealization.constantSection T M (op V.unop.left) x) := by
  unfold rawDirectGenerator
  rfl

private theorem rawDirectGenerator_eq {A : Type w} [CommRing A] (J : Ideal A) (U : C)
    (n : ℕ) (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    rawDirectGenerator T J U n M V x =
      sectionOver T U
        ((change (ConstantCompletion.quotient T A J n)).obj
          ((commutativeSiteConstantModuleFunctor T A).obj M)) V
        (tensorSection (ConstantCompletion.quotient T A J n)
          ((commutativeSiteConstantModuleFunctor T A).obj M) (op V.unop.left) 1
          (ConstantScalarRealization.constantSection T M (op V.unop.left) x)) := by
  unfold rawDirectGenerator directGenerator
  rfl

private theorem rawDirectGenerator_one {A : Type w} [CommRing A] (J : Ideal A) (U : C)
    (n : ℕ) (M : ModuleCat.{w} A) (V : (Over U)ᵒᵖ) (x : M) :
    natSection (T.over U) (directIso T (coefficientMap T A J) (projection T A J n) U
        (modelPresentationIso T A) (ConstantCompletion.quotient T A J n)
        (completionConeEq T J n)).hom M V
      (tensorSection ((T.overPullback CommRingCat U).map (projection T A J n))
        (((change (coefficientMap T A J)).obj
          ((modelPresentationFunctor T A).obj M)).over U) V 1
            (rawModelGenerator T J U M V x)) =
      rawDirectGenerator T J U n M V x := by
  rw [rawModelGenerator_eq, rawDirectGenerator_alias]
  exact directIso_generator T (coefficientMap T A J) (projection T A J n) U
    (modelPresentationIso T A) (ConstantCompletion.quotient T A J n)
    (completionConeEq T J n) M V
    (ConstantScalarRealization.constantSection T M (op V.unop.left) x)

section TerminalSections
variable {A : Type w} [CommRing A] (U : C)
  {S : Sheaf (T.over U) CommRingCat.{w}}
  (q : (constant T A).over U ⟶ S)

private def terminalSection (N : Mod S) (x : N.val.obj (op (Over.mk (𝟙 U)))) :
    ((res q ⋙ AdicQuotientSections.localSections T A U).obj N) := x

private theorem terminalSection_nat_map {D : Type*} [Category* D]
    {F G : D ⥤ Mod S} (α : F ⟶ G) (M : D)
    (x : (F.obj M).val.obj (op (Over.mk (𝟙 U)))) :
    moduleValue (whiskerRight α (res q ⋙ AdicQuotientSections.localSections T A U)) M
        (terminalSection T U q (F.obj M) x) =
      terminalSection T U q (G.obj M)
        (natSection (T.over U) α M (op (Over.mk (𝟙 U))) x) := by
  unfold moduleValue natSection
  rfl

private def normalizedSectionsAdjunction {F : ModuleCat.{w} A ⥤ Mod S}
    (α : F ≅ AdicQuotientSections.localConstant T A U ⋙ change q) :
    F ⊣ res q ⋙ AdicQuotientSections.localSections T A U :=
  ((AdicQuotientSections.localAdjunction T A U).comp
    (AdicPerfectModel.scalarAdjunction q)).ofNatIsoLeft α.symm

private theorem normalizedSectionsAdjunction_unit {F : ModuleCat.{w} A ⥤ Mod S}
    (α : F ≅ AdicQuotientSections.localConstant T A U ⋙ change q)
    (M : ModuleCat.{w} A) (x : M) :
    moduleValue (normalizedSectionsAdjunction T U q α).unit M x =
      terminalSection T U q (F.obj M)
        (natSection (T.over U) α.inv M (op (Over.mk (𝟙 U)))
          (tensorSection q ((AdicQuotientSections.localConstant T A U).obj M)
            (op (Over.mk (𝟙 U))) 1 (localGenerator T U M (op (Over.mk (𝟙 U))) x))) := by
  unfold moduleValue natSection
  rfl

private theorem normalizedSectionsAdjunction_unit_generator
    {F : ModuleCat.{w} A ⥤ Mod S}
    (α : F ≅ AdicQuotientSections.localConstant T A U ⋙ change q)
    (M : ModuleCat.{w} A) (x : M) (y : (F.obj M).val.obj (op (Over.mk (𝟙 U))))
    (hα : (natSection (T.over U) α.hom M (op (Over.mk (𝟙 U))) y) =
      tensorSection q ((AdicQuotientSections.localConstant T A U).obj M)
        (op (Over.mk (𝟙 U))) 1 (localGenerator T U M (op (Over.mk (𝟙 U))) x)) :
    moduleValue (normalizedSectionsAdjunction T U q α).unit M x =
      terminalSection T U q (F.obj M) y := by
  rw [normalizedSectionsAdjunction_unit, ← hα]
  exact congrArg (terminalSection T U q (F.obj M))
    (natSection_inv_hom (T.over U) α M (op (Over.mk (𝟙 U))) y)

attribute [irreducible] terminalSection normalizedSectionsAdjunction
private theorem terminalUnit_compat
    {S₀ S₁ : Sheaf (T.over U) CommRingCat.{w}}
    (q₀ : (constant T A).over U ⟶ S₀) (q₁ : (constant T A).over U ⟶ S₁)
    (τ : S₁ ⟶ S₀) {F₀ : ModuleCat.{w} A ⥤ Mod S₀}
    {F₁ : ModuleCat.{w} A ⥤ Mod S₁}
    (a₀ : F₀ ⊣ res q₀ ⋙ AdicQuotientSections.localSections T A U)
    (a₁ : F₁ ⊣ res q₁ ⋙ AdicQuotientSections.localSections T A U)
    (κ : res q₁ ⋙ AdicQuotientSections.localSections T A U ⟶
      change τ ⋙ res q₀ ⋙ AdicQuotientSections.localSections T A U)
    (θ : F₁ ⋙ change τ ≅ F₀)
    (g₀ : ∀ M : ModuleCat.{w} A, M → (F₀.obj M).val.obj (op (Over.mk (𝟙 U))))
    (g₁ : ∀ M : ModuleCat.{w} A, M → (F₁.obj M).val.obj (op (Over.mk (𝟙 U))))
    (hu₀ : ∀ M x, moduleValue a₀.unit M x = terminalSection T U q₀ (F₀.obj M) (g₀ M x))
    (hu₁ : ∀ M x, moduleValue a₁.unit M x = terminalSection T U q₁ (F₁.obj M) (g₁ M x))
    (hκ : ∀ N x, moduleValue κ N (terminalSection T U q₁ N x) =
      terminalSection T U q₀ ((change τ).obj N)
        (tensorSection τ N (op (Over.mk (𝟙 U))) 1 x))
    (hθ : ∀ M x, natSection (T.over U) θ.hom M (op (Over.mk (𝟙 U)))
      (tensorSection τ (F₁.obj M) (op (Over.mk (𝟙 U))) 1 (g₁ M x)) = g₀ M x)
    (M : ModuleCat.{w} A) :
    a₀.unit.app M = a₁.unit.app M ≫ κ.app (F₁.obj M) ≫
      (res q₀ ⋙ AdicQuotientSections.localSections T A U).map (θ.hom.app M) := by
  have h : a₀.unit = a₁.unit ≫ whiskerLeft F₁ κ ≫
      whiskerRight θ.hom (res q₀ ⋙ AdicQuotientSections.localSections T A U) := by
    apply moduleValue_ext
    intro N x
    rw [moduleValue_comp, moduleValue_comp, moduleValue_whiskerLeft, hu₀, hu₁, hκ]
    exact (congrArg (terminalSection T U q₀ (F₀.obj N)) (hθ N x)).symm.trans
      (terminalSection_nat_map T U q₀ θ.hom N
        (tensorSection τ (F₁.obj N) (op (Over.mk (𝟙 U))) 1 (g₁ N x))).symm
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using congr_app h M

end TerminalSections

private theorem generatorComparison_square (U : C)
    {B S : Sheaf (T.over U) CommRingCat.{w}} {D : Type*} [Category* D]
    {A : Type w} [CommRing A] (q₀ : (constant T A).over U ⟶ B)
    (q₁ : (constant T A).over U ⟶ S) (τ : S ⟶ B)
    (h : q₁ ≫ τ = q₀) (Q₀ Q₁ : D ⥤ ModuleCat.{w} A)
    (δ : Q₁ ⟶ Q₀) {F₀ : D ⥤ Mod B} {F₁ : D ⥤ Mod S}
    (β₀ : F₀ ⋙ res q₀ ≅ Q₀ ⋙ AdicQuotientSections.localConstant T A U)
    (β₁ : F₁ ⋙ res q₁ ≅ Q₁ ⋙ AdicQuotientSections.localConstant T A U)
    (θ : F₁ ⋙ change τ ≅ F₀) (M : D) (V : (Over U)ᵒᵖ) (z : Q₁.obj M)
    (x₀ : (F₀.obj M).val.obj V) (x₁ : (F₁.obj M).val.obj V)
    (h₀ : natSection (T.over U) β₀.inv M V
        (localGenerator T U (Q₀.obj M) V ((δ.app M).hom z)) =
      sectionRes (T.over U) q₀ (F₀.obj M) V x₀)
    (h₁ : natSection (T.over U) β₁.inv M V (localGenerator T U (Q₁.obj M) V z) =
      sectionRes (T.over U) q₁ (F₁.obj M) V x₁)
    (hθ : natSection (T.over U) θ.hom M V (tensorSection τ (F₁.obj M) V 1 x₁) = x₀) :
    natSection (T.over U)
        (whiskerRight δ (AdicQuotientSections.localConstant T A U) ≫ β₀.inv)
        M V (localGenerator T U (Q₁.obj M) V z) =
      natSection (T.over U)
        (β₁.inv ≫ whiskerLeft F₁ (insertionStep (T.over U) q₁ τ q₀ h) ≫
          whiskerRight θ.hom (res q₀)) M V (localGenerator T U (Q₁.obj M) V z) := by
  rw [natSection_comp, natSection_comp, natSection_comp, localGenerator_nat,
    natSection_whiskerLeft, h₀, h₁, insertionStep_section_res]
  exact (congrArg (sectionRes (T.over U) q₀ (F₀.obj M) V) hθ).symm.trans
    (res_natSection (T.over U) q₀ θ.hom M V (tensorSection τ (F₁.obj M) V 1 x₁)).symm

private theorem comparisonSquare_of_generators (U : C)
    {B S : Sheaf (T.over U) CommRingCat.{w}} {D : Type*} [Category* D]
    {A : Type w} [CommRing A] (q₀ : (constant T A).over U ⟶ B)
    (q₁ : (constant T A).over U ⟶ S) (τ : S ⟶ B)
    (h : q₁ ≫ τ = q₀) (Q₀ Q₁ : D ⥤ ModuleCat.{w} A)
    (δ : Q₁ ⟶ Q₀) {F₀ : D ⥤ Mod B} {F₁ : D ⥤ Mod S}
    (β₀ : F₀ ⋙ res q₀ ≅ Q₀ ⋙ AdicQuotientSections.localConstant T A U)
    (β₁ : F₁ ⋙ res q₁ ≅ Q₁ ⋙ AdicQuotientSections.localConstant T A U)
    (θ : F₁ ⋙ change τ ≅ F₀) (Z : D → Type w)
    (p : ∀ M, Z M → Q₁.obj M) (hp : ∀ M, Function.Surjective (p M))
    (hgen : ∀ (M : D) (V : (Over U)ᵒᵖ) (x : Z M),
      natSection (T.over U)
          (whiskerRight δ (AdicQuotientSections.localConstant T A U) ≫ β₀.inv)
          M V (localGenerator T U (Q₁.obj M) V (p M x)) =
        natSection (T.over U)
          (β₁.inv ≫ whiskerLeft F₁ (insertionStep (T.over U) q₁ τ q₀ h) ≫
            whiskerRight θ.hom (res q₀)) M V (localGenerator T U (Q₁.obj M) V (p M x)))
    (M : D) :
    (AdicQuotientSections.localConstant T A U).map (δ.app M) ≫ β₀.inv.app M =
      β₁.inv.app M ≫ (insertionStep (T.over U) q₁ τ q₀ h).app (F₁.obj M) ≫
        (res q₀).map (θ.hom.app M) := by
  have hn := localNatural_ext_surjective T U Q₁ Z p hp
    (whiskerRight δ (AdicQuotientSections.localConstant T A U) ≫ β₀.inv)
    (β₁.inv ≫ whiskerLeft F₁ (insertionStep (T.over U) q₁ τ q₀ h) ≫
      whiskerRight θ.hom (res q₀)) hgen
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using congr_app hn M

end ModelPresentation

end AlgebraicGeometry.Scheme
