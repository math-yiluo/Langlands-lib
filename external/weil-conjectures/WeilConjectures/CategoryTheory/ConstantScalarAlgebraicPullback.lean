/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import all WeilConjectures.CategoryTheory.ConstantLeftModuleTransport
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact

/-! # Algebraic presentation of fixed-scalar inverse image

Source: Stacks Project, Modules on Sites, Tags 03CY and 03D2; Sites, Tag 00YV.
-/

@[expose] public section
set_option autoImplicit false
universe w
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Functor.sheafPullbackConstruction
namespace CategoryTheory.ConstantScalarRestriction

noncomputable section

variable {C D : Type w} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]

private abbrev sets (J : GrothendieckTopology C) (A : Type w) [CommRing A] :=
  (sheafCompose J (forget CommRingCat.{w})).obj (ring J A)

private abbrev base (J : GrothendieckTopology C) (A : Type w) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (ring J A)

private abbrev moduleSets (J : GrothendieckTopology C) (A : Type w) [CommRing A] :=
  SheafOfModules.toSheaf (base J A) ⋙ sheafCompose J (forget AddCommGrpCat.{w})

private def scalar (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    (U : Cᵒᵖ) (a : A) : (ring J A).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a

private def coefficientMap (A : Type w) [CommRing A] :
    ring J A ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J K).obj (ring K A) :=
  ((sheafificationAdjunction J CommRingCat.{w}).homEquiv _ _).symm
    { app := fun U ↦
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U)
      naturality := fun _ _ f ↦
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).naturality (F.op.map f) }

omit [RepresentablyFlat F] in
private theorem coefficientMap_scalar (A : Type w) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (coefficientMap J K F A).hom.app U (scalar J A U a) = scalar K A (F.op.obj U) a := by
  have h' := ((sheafificationAdjunction J CommRingCat.{w}).homEquiv
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{w} J K).obj (ring K A))).apply_symm_apply
    (show (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ _ from
      { app := fun U ↦
          (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U)
        naturality := fun _ _ f ↦
          (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).naturality
            (F.op.map f) })
  exact congrArg (fun t ↦ t.app U a) h'

private def constantIso :
    constantSheaf J (Type w) ⋙ sheafPullback F (Type w) J K ≅
      constantSheaf K (Type w) :=
  CategoryTheory.constantComparison J K (sheafPullback F (Type w) J K)
    (F.sheafPushforwardContinuous (Type w) J K)
    (sheafAdjunctionContinuous F (Type w) J K)

private theorem constantMap_apply (X : Type w) (a : X) (U : Dᵒᵖ)
    (t : ((constantSheaf K (Type w)).obj PUnit.{w + 1}).obj.obj U) :
    (((constantSheaf K (Type w)).map
      (TypeCat.ofHom (fun _ : PUnit.{w + 1} ↦ a))).hom.app U) t =
        (toSheafify K ((Functor.const Dᵒᵖ).obj X)).app U a := by
  let P := (Functor.const Dᵒᵖ).obj PUnit.{w + 1}
  have : IsIso (toSheafify K P) :=
    isIso_toSheafify K (Presheaf.isSheaf_of_isTerminal K Types.isTerminalPUnit)
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((toSheafify K P).app U)).2 t
  exact (congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality K ((Functor.const Dᵒᵖ).map
      (TypeCat.ofHom (fun _ : PUnit.{w + 1} ↦ a))))).symm

private theorem constantIso_unit (X : Type w) (U : Cᵒᵖ) (x : X) :
    ((constantIso J K F).hom.app X).hom.app (F.op.obj U)
      (((sheafAdjunctionContinuous F (Type w) J K).unit.app
        ((constantSheaf J (Type w)).obj X)).hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x)) =
      (toSheafify K ((Functor.const Dᵒᵖ).obj X)).app (F.op.obj U) x := by
  let f : PUnit.{w + 1} ⟶ X := TypeCat.ofHom (fun _ ↦ x)
  let p := (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{w + 1})).app U PUnit.unit
  have hf := CategoryTheory.constantMap_unit J PUnit.{w + 1} X (fun _ ↦ x) U PUnit.unit
  have hn := (sheafAdjunctionContinuous F (Type w) J K).unit.naturality
    ((constantSheaf J (Type w)).map f)
  have he := (constantIso J K F).hom.naturality f
  have h := congrArg (fun t ↦ t.hom.app U p) hn
  have h' := congrArg (fun t ↦ t.hom.app (F.op.obj U)
    (((sheafAdjunctionContinuous F (Type w) J K).unit.app
      ((constantSheaf J (Type w)).obj PUnit.{w + 1})).hom.app U p)) he
  change (((sheafAdjunctionContinuous F (Type w) J K).unit.app
    ((constantSheaf J (Type w)).obj X)).hom.app U)
      (((constantSheaf J (Type w)).map f).hom.app U p) =
    ((sheafPullback F (Type w) J K).map ((constantSheaf J (Type w)).map f)).hom.app
      (F.op.obj U) (((sheafAdjunctionContinuous F (Type w) J K).unit.app
        ((constantSheaf J (Type w)).obj PUnit.{w + 1})).hom.app U p) at h
  change ((constantIso J K F).hom.app X).hom.app (F.op.obj U)
    (((sheafPullback F (Type w) J K).map ((constantSheaf J (Type w)).map f)).hom.app
      (F.op.obj U) _) =
    (((constantSheaf K (Type w)).map f).hom.app (F.op.obj U))
      (((constantIso J K F).hom.app PUnit.{w + 1}).hom.app (F.op.obj U) _) at h'
  erw [hf] at h
  exact (congrArg (((constantIso J K F).hom.app X).hom.app (F.op.obj U)) h).trans
    (h'.trans (constantMap_apply K X x _ _))

private def ringIso (A : Type w) [CommRing A] :
    sets K A ≅ (sheafPullback F (Type w) J K).obj (sets J A) :=
  (constantCommuteCompose K (forget CommRingCat.{w})).app (CommRingCat.of A) ≪≫
    ((constantIso J K F).app A).symm ≪≫
      (sheafPullback F (Type w) J K).mapIso
        (((constantCommuteCompose J (forget CommRingCat.{w})).app
          (CommRingCat.of A)).symm)

private theorem forgetConstant_unit (A : Type w) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget CommRingCat.{w})).app
      (CommRingCat.of A)).inv).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a) = scalar J A U a := by
  have h := sheafComposeIso_hom_fac J (forget CommRingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of A) (forget CommRingCat.{w})).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj A)) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ (CommRingCat.of A)
      (forget CommRingCat.{w})).inv) ≫
    (sheafifyComposeIso J (forget CommRingCat.{w})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom).app U) a = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

private theorem forgetConstant_hom_unit (A : Type w) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget CommRingCat.{w})).app
      (CommRingCat.of A)).hom).hom.app U (scalar J A U a) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := by
  rw [← forgetConstant_unit J A U a]
  exact congrArg (fun f ↦ f.hom.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))
      ((constantCommuteCompose J (forget CommRingCat.{w})).app
        (CommRingCat.of A)).inv_hom_id

private theorem ringIso_scalar (A : Type w) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (ringIso J K F A).hom.hom.app (F.op.obj U) (scalar K A (F.op.obj U) a) =
      ((sheafAdjunctionContinuous F (Type w) J K).unit.app (sets J A)).hom.app U
        (scalar J A U a) := by
  let c := (constantCommuteCompose J (forget CommRingCat.{w})).app (CommRingCat.of A)
  let e := (constantIso J K F).app A
  have he := constantIso_unit J K F A U a
  have hei := congrArg (e.inv.hom.app (F.op.obj U)) he
  have hi := congrArg (fun f ↦ f.hom.app (F.op.obj U)
    (((sheafAdjunctionContinuous F (Type w) J K).unit.app
      ((constantSheaf J (Type w)).obj A)).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))) e.hom_inv_id
  change e.inv.hom.app (F.op.obj U) (e.hom.hom.app (F.op.obj U)
    (((sheafAdjunctionContinuous F (Type w) J K).unit.app
      ((constantSheaf J (Type w)).obj A)).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))) = _ at hei
  change e.inv.hom.app (F.op.obj U) (e.hom.hom.app (F.op.obj U)
    (((sheafAdjunctionContinuous F (Type w) J K).unit.app
      ((constantSheaf J (Type w)).obj A)).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))) = _ at hi
  rw [hi] at hei
  have hn := congrArg (fun t ↦ t.hom.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))
      ((sheafAdjunctionContinuous F (Type w) J K).unit.naturality c.inv)
  change ((sheafAdjunctionContinuous F (Type w) J K).unit.app (sets J A)).hom.app U
    (c.inv.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)) =
    ((sheafPullback F (Type w) J K).map c.inv).hom.app (F.op.obj U)
      (((sheafAdjunctionContinuous F (Type w) J K).unit.app
        ((constantSheaf J (Type w)).obj A)).hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)) at hn
  change ((sheafPullback F (Type w) J K).map c.inv).hom.app (F.op.obj U)
    (e.inv.hom.app (F.op.obj U) _) = _
  change (((sheafAdjunctionContinuous F (Type w) J K).unit.app
    ((constantSheaf J (Type w)).obj A)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)) =
    e.inv.hom.app (F.op.obj U)
      ((toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) a) at hei
  exact (congrArg (fun z ↦
    ((sheafPullback F (Type w) J K).map c.inv).hom.app (F.op.obj U)
      (e.inv.hom.app (F.op.obj U) z))
        (forgetConstant_hom_unit K A (F.op.obj U) a)).trans
    ((congrArg (((sheafPullback F (Type w) J K).map c.inv).hom.app (F.op.obj U))
      hei.symm).trans (hn.symm.trans (congrArg
        (((sheafAdjunctionContinuous F (Type w) J K).unit.app (sets J A)).hom.app U)
          (forgetConstant_unit J A U a))))

private def ringPresentation (A : Type w) [CommRing A] :
    SheafPullbackUnitPresentation (F := F) (sets J A) (sets K A) where
  unit := (sheafCompose J (forget CommRingCat.{w})).map (coefficientMap J K F A)
  iso := ringIso J K F A
  equation := by
    have h : (sheafCompose J (forget CommRingCat.{w})).map
        (coefficientMap J K F A) ≫
          (F.sheafPushforwardContinuous (Type w) J K).map (ringIso J K F A).hom =
        (sheafAdjunctionContinuous F (Type w) J K).unit.app (sets J A) := by
      let c := (constantCommuteCompose J (forget CommRingCat.{w})).app (CommRingCat.of A)
      apply (cancel_epi c.inv).1
      apply Sheaf.hom_ext
      apply sheafify_hom_ext J _ _
        ((F.sheafPushforwardContinuous (Type w) J K).obj
          ((sheafPullback F (Type w) J K).obj (sets J A))).property
      ext U a
      change (ringIso J K F A).hom.hom.app (F.op.obj U)
        ((coefficientMap J K F A).hom.app U (c.inv.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))) =
        ((sheafAdjunctionContinuous F (Type w) J K).unit.app (sets J A)).hom.app U
          (c.inv.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))
      rw [forgetConstant_unit J, coefficientMap_scalar, ringIso_scalar]
    intro U a
    exact congrArg (fun t ↦ t.hom.app U a) h

private def canonicalPresentation (S : Sheaf J (Type w)) :
    SheafPullbackUnitPresentation (F := F) S
      ((sheafPullback F (Type w) J K).obj S) where
  unit := (sheafAdjunctionContinuous F (Type w) J K).unit.app S
  iso := Iso.refl _
  equation := fun _ _ ↦ rfl

omit [RepresentablyFlat F] in
private theorem unit_map {S X : Sheaf J (Type w)} {T : Sheaf K (Type w)}
    (p : SheafPullbackUnitPresentation (F := F) S T) (a : X ⟶ S)
    (U : Cᵒᵖ) (x : X.obj.obj U) :
    ((sheafPullback F (Type w) J K).map a ≫ p.iso.inv).hom.app (F.op.obj U)
      (((sheafAdjunctionContinuous F (Type w) J K).unit.app X).hom.app U x) =
        p.unit.hom.app U (a.hom.app U x) := by
  have hn := congrArg (fun t ↦ t.hom.app U x)
    ((sheafAdjunctionContinuous F (Type w) J K).unit.naturality a)
  change ((sheafAdjunctionContinuous F (Type w) J K).unit.app S).hom.app U
    (a.hom.app U x) =
    ((sheafPullback F (Type w) J K).map a).hom.app (F.op.obj U)
      (((sheafAdjunctionContinuous F (Type w) J K).unit.app X).hom.app U x) at hn
  have hi := congrArg (fun t ↦ t.hom.app (F.op.obj U)
    (p.unit.hom.app U (a.hom.app U x))) p.iso.hom_inv_id
  change p.iso.inv.hom.app (F.op.obj U)
    (p.iso.hom.hom.app (F.op.obj U) (p.unit.hom.app U (a.hom.app U x))) =
      p.unit.hom.app U (a.hom.app U x) at hi
  change p.iso.inv.hom.app (F.op.obj U)
    (((sheafPullback F (Type w) J K).map a).hom.app (F.op.obj U)
      (((sheafAdjunctionContinuous F (Type w) J K).unit.app X).hom.app U x)) = _
  exact (congrArg (p.iso.inv.hom.app (F.op.obj U)) hn.symm).trans
    ((congrArg (p.iso.inv.hom.app (F.op.obj U))
      (p.equation U (a.hom.app U x)).symm).trans hi)

omit [RepresentablyFlat F] in
private theorem transport_eq {S X : Sheaf J (Type w)} {T : Sheaf K (Type w)}
    (p : SheafPullbackUnitPresentation (F := F) S T) (a : X ⟶ S)
    (b : (sheafPullback F (Type w) J K).obj X ⟶ T)
    (h : ∀ (U : Cᵒᵖ) (x : X.obj.obj U),
      p.unit.hom.app U (a.hom.app U x) =
        b.hom.app (F.op.obj U)
          (((sheafAdjunctionContinuous F (Type w) J K).unit.app X).hom.app U x)) :
    (sheafPullback F (Type w) J K).map a ≫ p.iso.inv = b := by
  apply (canonicalPresentation J K F X).hom_ext
  intro U x
  exact (unit_map J K F p a U x).trans (h U x)

private def binaryArrow {X Y Z T : Sheaf K (Type w)}
    (o : ∀ U : Dᵒᵖ, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (ho : ∀ (U V : Dᵒᵖ) (f : U ⟶ V) (x : X.obj.obj U) (y : Y.obj.obj U),
      o V (X.obj.map f x) (Y.obj.map f y) = Z.obj.map f (o U x y))
    (a : T ⟶ X) (b : T ⟶ Y) : T ⟶ Z :=
  ⟨{ app := fun U ↦ ↾fun x ↦ o U (a.hom.app U x) (b.hom.app U x)
     naturality := by
       intro U V f
       ext x
       change o V (a.hom.app V (T.obj.map f x)) (b.hom.app V (T.obj.map f x)) = _
       have ha := CategoryTheory.congr_fun (a.hom.naturality f) x
       have hb := CategoryTheory.congr_fun (b.hom.naturality f) x
       change a.hom.app V (T.obj.map f x) = X.obj.map f (a.hom.app U x) at ha
       change b.hom.app V (T.obj.map f x) = Y.obj.map f (b.hom.app U x) at hb
       rw [ha, hb]
       exact ho U V f _ _ }⟩

private def constantArrow {Z T : Sheaf K (Type w)}
    (z : ∀ U : Dᵒᵖ, Z.obj.obj U)
    (hz : ∀ (U V : Dᵒᵖ) (f : U ⟶ V), z V = Z.obj.map f (z U)) : T ⟶ Z :=
  ⟨{ app := fun U ↦ ↾fun _ ↦ z U
     naturality := by intro U V f; ext x; exact hz U V f }⟩

private def ringMap (A : Type w) [CommRing A] :
    base J A ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj (base K A) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (coefficientMap J K F A)

private def moduleUnit (A : Type w) [CommRing A] (M : Modules J A) :
    (moduleSets J A).obj M ⟶ (F.sheafPushforwardContinuous (Type w) J K).obj
      ((moduleSets K A).obj ((SheafOfModules.pullback (ringMap J K F A)).obj M)) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).map
    ((SheafOfModules.toSheaf (base J A)).map
      ((SheafOfModules.pullbackPushforwardAdjunction (ringMap J K F A)).unit.app M))

private theorem moduleComparison (A : Type w) [CommRing A] :
    ∃ e : SheafOfModules.pullback (ringMap J K F A) ⋙ moduleSets K A ≅
        moduleSets J A ⋙ sheafPullback F (Type w) J K,
      ∀ (M : Modules J A) (U : Cᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).hom.app (F.op.obj U) ((moduleUnit J K F A M).hom.app U x) =
          ((sheafAdjunctionContinuous F (Type w) J K).unit.app
            ((moduleSets J A).obj M)).hom.app U x := by
  obtain ⟨e, he⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (ringMap J K F A) (ringPresentation J K F A) rfl
  let ea := sheafPullbackForgetIso J K F (forget AddCommGrpCat.{w})
  refine ⟨Functor.isoWhiskerRight e (sheafCompose K (forget AddCommGrpCat.{w})) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf (base J A)) ea, ?_⟩
  intro M U x
  have h := congrArg (fun t ↦ t.hom.app U x) (he M)
  have h' := congrArg (fun t ↦ t.hom.app U x)
    (sheafPullbackForgetIso_unit J K F (forget AddCommGrpCat.{w})
      ((SheafOfModules.toSheaf (base J A)).obj M))
  exact (congrArg ((ea.hom.app ((SheafOfModules.toSheaf (base J A)).obj M)).hom.app
    (F.op.obj U)) h).trans h'

private theorem algebraicPresentation (A : Type w) [CommRing A] :
    ∃ I : SheafOfModules.AlgebraicInverseImage
        (sheafPullback F (Type w) J K) (ring J A) (ring K A),
      I.modules = SheafOfModules.pullback (ringMap J K F A) := by
  obtain ⟨e, he⟩ := moduleComparison J K F A
  let P := SheafOfModules.pullback (ringMap J K F A)
  let pr := ringPresentation J K F A
  let pm (M : Modules J A) : SheafPullbackUnitPresentation (F := F)
      ((moduleSets J A).obj M) ((moduleSets K A).obj (P.obj M)) :=
    { unit := moduleUnit J K F A M
      iso := e.app M
      equation := he M }
  refine ⟨{
    ringUnderlying := pr.iso.symm
    modules := P
    moduleUnderlying := e
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_ }, rfl⟩
  · intro T a b t ht V x
    let c := binaryArrow K (X := sets K A) (Y := sets K A) (Z := sets K A)
      (fun U (x y : (ring K A).obj.obj U) ↦ x + y)
      (by
        intro U V f x y
        have h := map_add ((ring K A).obj.map f).hom
          (@id ((ring K A).obj.obj U) x) (@id ((ring K A).obj.obj U) y)
        exact h.symm)
      ((sheafPullback F (Type w) J K).map a ≫ pr.iso.inv)
      ((sheafPullback F (Type w) J K).map b ≫ pr.iso.inv)
    have h := transport_eq J K F pr t c (by
      intro U z
      have ha := unit_map J K F pr a U z
      have hb := unit_map J K F pr b U z
      have ht' : @id ((ring J A).obj.obj U) (t.hom.app U z) =
          @id ((ring J A).obj.obj U) (a.hom.app U z) +
            @id ((ring J A).obj.obj U) (b.hom.app U z) := ht U z
      have hφ := congrArg ((coefficientMap J K F A).hom.app U).hom ht'
      have hop := map_add ((coefficientMap J K F A).hom.app U).hom
        (@id ((ring J A).obj.obj U) (a.hom.app U z))
        (@id ((ring J A).obj.obj U) (b.hom.app U z))
      exact hφ.trans (hop.trans
        (congrArg₂ (fun (x y : (ring K A).obj.obj (F.op.obj U)) ↦ x + y)
          ha.symm hb.symm)))
    exact congrArg (fun f ↦ f.hom.app V x) h
  · intro T a b t ht V x
    let c := binaryArrow K (X := sets K A) (Y := sets K A) (Z := sets K A)
      (fun U (x y : (ring K A).obj.obj U) ↦ x * y)
      (by
        intro U V f x y
        have h := map_mul ((ring K A).obj.map f).hom
          (@id ((ring K A).obj.obj U) x) (@id ((ring K A).obj.obj U) y)
        exact h.symm)
      ((sheafPullback F (Type w) J K).map a ≫ pr.iso.inv)
      ((sheafPullback F (Type w) J K).map b ≫ pr.iso.inv)
    have h := transport_eq J K F pr t c (by
      intro U z
      have ha := unit_map J K F pr a U z
      have hb := unit_map J K F pr b U z
      have ht' : @id ((ring J A).obj.obj U) (t.hom.app U z) =
          @id ((ring J A).obj.obj U) (a.hom.app U z) *
            @id ((ring J A).obj.obj U) (b.hom.app U z) := ht U z
      have hφ := congrArg ((coefficientMap J K F A).hom.app U).hom ht'
      have hop := map_mul ((coefficientMap J K F A).hom.app U).hom
        (@id ((ring J A).obj.obj U) (a.hom.app U z))
        (@id ((ring J A).obj.obj U) (b.hom.app U z))
      exact hφ.trans (hop.trans
        (congrArg₂ (fun (x y : (ring K A).obj.obj (F.op.obj U)) ↦ x * y)
          ha.symm hb.symm)))
    exact congrArg (fun f ↦ f.hom.app V x) h
  · intro T a ha V x
    let c : (sheafPullback F (Type w) J K).obj T ⟶ sets K A :=
      constantArrow K (fun U ↦ (0 : (ring K A).obj.obj U))
        (fun _ _ f ↦ (map_zero ((ring K A).obj.map f).hom).symm)
    have h := transport_eq J K F pr a c (by
      intro U z
      have ha' : @id ((ring J A).obj.obj U) (a.hom.app U z) = 0 := ha U z
      exact (congrArg ((coefficientMap J K F A).hom.app U).hom ha').trans
        (map_zero ((coefficientMap J K F A).hom.app U).hom))
    exact congrArg (fun f ↦ f.hom.app V x) h
  · intro T a ha V x
    let c : (sheafPullback F (Type w) J K).obj T ⟶ sets K A :=
      constantArrow K (fun U ↦ (1 : (ring K A).obj.obj U))
        (fun _ _ f ↦ (map_one ((ring K A).obj.map f).hom).symm)
    have h := transport_eq J K F pr a c (by
      intro U z
      have ha' : @id ((ring J A).obj.obj U) (a.hom.app U z) = 1 := ha U z
      exact (congrArg ((coefficientMap J K F A).hom.app U).hom ha').trans
        (map_one ((coefficientMap J K F A).hom.app U).hom))
    exact congrArg (fun f ↦ f.hom.app V x) h
  · intro M T a b t ht V x
    let c := binaryArrow K (X := (moduleSets K A).obj (P.obj M))
      (Y := (moduleSets K A).obj (P.obj M)) (Z := (moduleSets K A).obj (P.obj M))
      (fun U (x y : (P.obj M).val.obj U) ↦ x + y)
      (by
        intro U V f x y
        have h := map_add ((P.obj M).val.map f).hom
          (@id ((P.obj M).val.obj U) x) (@id ((P.obj M).val.obj U) y)
        exact h.symm)
      ((sheafPullback F (Type w) J K).map a ≫ (pm M).iso.inv)
      ((sheafPullback F (Type w) J K).map b ≫ (pm M).iso.inv)
    have h := transport_eq J K F (pm M) t c (by
      intro U z
      have ha := unit_map J K F (pm M) a U z
      have hb := unit_map J K F (pm M) b U z
      have ht' : @id (M.val.obj U) (t.hom.app U z) =
          @id (M.val.obj U) (a.hom.app U z) + @id (M.val.obj U) (b.hom.app U z) := ht U z
      let u := ((SheafOfModules.pullbackPushforwardAdjunction
        (ringMap J K F A)).unit.app M).val.app U
      have hφ := congrArg u.hom ht'
      have hop := map_add u.hom
        (@id (M.val.obj U) (a.hom.app U z)) (@id (M.val.obj U) (b.hom.app U z))
      exact hφ.trans (hop.trans
        (congrArg₂ (fun (x y : (P.obj M).val.obj (F.op.obj U)) ↦ x + y)
          ha.symm hb.symm)))
    exact congrArg (fun f ↦ f.hom.app V x) h
  · intro M T a ha V x
    let c : (sheafPullback F (Type w) J K).obj T ⟶ (moduleSets K A).obj (P.obj M) :=
      constantArrow K (fun U ↦ (0 : (P.obj M).val.obj U))
        (fun _ _ f ↦ (map_zero ((P.obj M).val.map f).hom).symm)
    have h := transport_eq J K F (pm M) a c (by
      intro U z
      have ha' : @id (M.val.obj U) (a.hom.app U z) = 0 := ha U z
      let u := ((SheafOfModules.pullbackPushforwardAdjunction
        (ringMap J K F A)).unit.app M).val.app U
      exact (congrArg u.hom ha').trans (map_zero u.hom))
    exact congrArg (fun f ↦ f.hom.app V x) h
  · intro M T a b t ht V x
    let c := binaryArrow K (X := sets K A)
      (Y := (moduleSets K A).obj (P.obj M)) (Z := (moduleSets K A).obj (P.obj M))
      (fun U (r : (ring K A).obj.obj U) (x : (P.obj M).val.obj U) ↦ r • x)
      (by
        intro U V f r x
        have h := (P.obj M).val.map_smul f r x
        exact h.symm)
      ((sheafPullback F (Type w) J K).map a ≫ pr.iso.inv)
      ((sheafPullback F (Type w) J K).map b ≫ (pm M).iso.inv)
    have h := transport_eq J K F (pm M) t c (by
      intro U z
      have ha := unit_map J K F pr a U z
      have hb := unit_map J K F (pm M) b U z
      have ht' : @id (M.val.obj U) (t.hom.app U z) =
          @id ((ring J A).obj.obj U) (a.hom.app U z) •
            @id (M.val.obj U) (b.hom.app U z) := ht U z
      let u := ((SheafOfModules.pullbackPushforwardAdjunction
        (ringMap J K F A)).unit.app M).val.app U
      have hφ := congrArg u.hom ht'
      have hop := u.hom.map_smul
        (@id ((ring J A).obj.obj U) (a.hom.app U z)) (@id (M.val.obj U) (b.hom.app U z))
      exact hφ.trans (hop.trans
        (congrArg₂ (fun (r : (ring K A).obj.obj (F.op.obj U))
          (x : (P.obj M).val.obj (F.op.obj U)) ↦ r • x) ha.symm hb.symm)))
    exact congrArg (fun f ↦ f.hom.app V x) h

private theorem restriction_scalar (A : Type w) [CommRing A]
    (M : Modules J A) (U : Cᵒᵖ) (a : A) (x : M.val.obj U) :
    @SMul.smul A (((restriction J A).obj M).obj.obj U) inferInstance a x =
      scalar J A U a • x := by
  change ((constantCommuteCompose J (forget₂ CommRingCat.{w} RingCat.{w})).inv.app
    (CommRingCat.of A)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) • x = _
  congr 1
  have hf := congrArg (fun f ↦ f.app U a)
    (sheafComposeIso_hom_fac J (forget₂ CommRingCat.{w} RingCat.{w})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
  have hp := congrArg (fun f ↦ f.app U a) (toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget₂ CommRingCat.{w} RingCat.{w})).hom.app
      (CommRingCat.of A)))
  dsimp at hp
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{w} RingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) _ = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget₂ CommRingCat.{w} RingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) z) hp.symm).trans hf

private def rightComparison (A : Type w) [CommRing A] :
    SheafOfModules.pushforward (ringMap J K F A) ⋙ restriction J A ≅
      restriction K A ⋙ F.sheafPushforwardContinuous (ModuleCat.{w} A) J K := by
  refine NatIso.ofComponents (fun N ↦ {
    hom := { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction J A).obj
          ((SheafOfModules.pushforward (ringMap J K F A)).obj N)).obj.obj U)
        (Y := ((restriction K A).obj N).obj.obj (F.op.obj U)) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }
      naturality := by intro U V f; ext x; rfl } }
    inv := { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction K A).obj N).obj.obj (F.op.obj U))
        (Y := ((restriction J A).obj
          ((SheafOfModules.pushforward (ringMap J K F A)).obj N)).obj.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }
      naturality := by intro U V f; ext x; rfl } }
    hom_inv_id := by ext U x; rfl
    inv_hom_id := by ext U x; rfl }) (by intro M N f; ext U x; rfl)
  · intro a x
    have hJ := restriction_scalar J A
      ((SheafOfModules.pushforward (ringMap J K F A)).obj N) U a x
    have hK := restriction_scalar K A N (F.op.obj U) a x
    have hφ := congrArg (fun r : (ring K A).obj.obj (F.op.obj U) ↦
      r • (show N.val.obj (F.op.obj U) from x))
      (coefficientMap_scalar J K F A U a)
    exact hJ.trans (hφ.trans hK.symm)
  · intro a x
    have hJ := restriction_scalar J A
      ((SheafOfModules.pushforward (ringMap J K F A)).obj N) U a x
    have hK := restriction_scalar K A N (F.op.obj U) a x
    have hφ := congrArg (fun r : (ring K A).obj.obj (F.op.obj U) ↦
      r • (show N.val.obj (F.op.obj U) from x))
      (coefficientMap_scalar J K F A U a)
    exact hK.trans (hφ.symm.trans hJ.symm)

omit [RepresentablyFlat F] in
private theorem pullbackComparison (A : Type w) [CommRing A] :
    Nonempty (SheafOfModules.pullback (ringMap J K F A) ⋙ restriction K A ≅
      restriction J A ⋙ sheafPullback F (ModuleCat.{w} A) J K) := by
  let eJ := (restriction J A).asEquivalence
  let eK := (restriction K A).asEquivalence
  let P := SheafOfModules.pushforward (ringMap J K F A)
  let R := F.sheafPushforwardContinuous (ModuleCat.{w} A) J K
  let rho := rightComparison J K F A
  let er : eK.inverse ⋙ P ≅ R ⋙ eJ.inverse :=
    Functor.isoWhiskerLeft (eK.inverse ⋙ P) eJ.unitIso ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft eK.inverse rho) eJ.inverse ≪≫
        Functor.isoWhiskerRight eK.counitIso (R ⋙ eJ.inverse)
  let a := ((SheafOfModules.pullbackPushforwardAdjunction (ringMap J K F A)).comp
    eK.toAdjunction).ofNatIsoRight er
  exact ⟨a.leftAdjointUniq (eJ.toAdjunction.comp
    (sheafAdjunctionContinuous F (ModuleCat.{w} A) J K))⟩

/-- The usual fixed-scalar sheaf inverse image is the algebraic inverse image over
constant coefficient rings, after the normalized constant-scalar equivalences.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03D2; Sites, Tag 00YV.
(auxiliary; not a blueprint node).

Proof: construct the coefficient homomorphism through the commutative-ring
sheafification adjunction and normalize the constant-object comparison on constant
scalars. This gives a ring unit presentation. The existing normalized module
inverse-image adjunction identifies Mathlib's module pullback with underlying set
inverse image. Check all seven operation graphs on the adjunction units, using the
coefficient homomorphism and the linear module unit. Transport this presentation
through the canonical equal-universe ULift isomorphisms. Finally, scalar-restricted
module pushforward agrees with fixed-scalar pushforward by the identity on sections;
the coefficient homomorphism equation on constants proves its linearity. Uniqueness
of left adjoints gives the required pullback comparison. No flatness property is used. -/
theorem exists_constantScalarAlgebraicPullback
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]
    (A : Type w) [CommRing A] :
    ∃ I : SheafOfModules.AlgebraicInverseImageOfUniverses.{w, w, w, w, w, w}
        (sheafPullback F (Type w) J K) (ring J A) (ring K A),
      Nonempty (I.modules ⋙ restriction K A ≅
        restriction J A ⋙ sheafPullback F (ModuleCat.{w} A) J K) := by
  obtain ⟨I, hI⟩ := algebraicPresentation J K F A
  let IU := CategoryTheory.GeometricMorphism.inverseImageUniverses.{w, w, w, w, w} I
  refine ⟨IU, ?_⟩
  change Nonempty (I.modules ⋙ restriction K A ≅
    restriction J A ⋙ sheafPullback F (ModuleCat.{w} A) J K)
  rw [hI]
  exact pullbackComparison J K F A

end

end CategoryTheory.ConstantScalarRestriction
