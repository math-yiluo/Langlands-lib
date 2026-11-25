/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomHomotopyExact
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison

/-! # Contravariant exactness of derived internal Hom

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

attribute [local irreducible] CategoryTheory.homComplexFunctor CategoryTheory.homComplexπ
  CategoryTheory.derivedInternalHom

private noncomputable def rightOpIso {A B : Type*} [Category A] [Category B]
    {F G : Aᵒᵖ ⥤ B} (e : F ≅ G) : G.rightOp ≅ F.rightOp :=
  NatIso.ofComponents (fun X ↦ (e.app (op X)).op) (by
    intro X Y f
    apply Quiver.Hom.unop_inj
    exact (e.hom.naturality f.op).symm)

private noncomputable def nativeBifunctorIso
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] [HasCountableProducts A]
    [(MonoidalClosed.internalHom (C := A)).Additive]
    [∀ X : Aᵒᵖ, ((MonoidalClosed.internalHom (C := A)).obj X).Additive]
    (K I : CochainComplex A ℤ) :
    CochainComplex.internalHomObj K I ≅
      CochainComplex.bifunctorHomObj MonoidalClosed.internalHom K I := Iso.refl _

private theorem nativeBifunctorIso_π
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] [HasCountableProducts A]
    [(MonoidalClosed.internalHom (C := A)).Additive]
    [∀ X : Aᵒᵖ, ((MonoidalClosed.internalHom (C := A)).obj X).Additive]
    (K I : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q) :
    (nativeBifunctorIso K I).hom.f n ≫
        CochainComplex.bifunctorHomπ MonoidalClosed.internalHom K I n p q h =
      CochainComplex.internalHomπ K I n p q h := Category.id_comp _

private theorem internalHomMapApp_eq_pre
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    {L L' : A} (f : L' ⟶ L) (N : A) :
    ((MonoidalClosed.internalHom (C := A)).map f.op).app N =
      (MonoidalClosed.pre f).app N := rfl

section
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

private abbrev Modules := SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

attribute [local instance 10000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive

private instance ringedInternalHomContravariantExactInst1
    : IsGrothendieckAbelian.{u} (Modules J R) :=
  SheafOfModules.isGrothendieckAbelian _

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

private instance ringedInternalHomContravariantExactInst2
    : MonoidalPreadditive (Modules J R) := (SheafOfModules.tensorClosed R).1.some

private instance internalHom_additive :
    (MonoidalClosed.internalHom (C := Modules J R)).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    exact MonoidalClosed.pre_add_app f.unop g.unop Z

private instance internalHom_obj_additive (X : (Modules J R)ᵒᵖ) :
    (MonoidalClosed.internalHom.obj X).Additive :=
  inferInstanceAs (ihom X.unop).Additive

attribute [local irreducible] SheafOfModules.homObj SheafOfModules.homObjMap
  MonoidalClosed.pre

-- A fixed name prevents repeated expansion of the closed structure in conversion goals.
private noncomputable def ordinaryModuleHom : (Modules J R)ᵒᵖ ⥤ Modules J R ⥤ Modules J R :=
  MonoidalClosed.internalHom

private instance ordinaryModuleHom_additive : (ordinaryModuleHom J R).Additive :=
  internalHom_additive J R

private instance ordinaryModuleHom_obj_additive (X : (Modules J R)ᵒᵖ) :
    ((ordinaryModuleHom J R).obj X).Additive := internalHom_obj_additive J R X

private theorem moduleInternalHomMapApp {L L' : Modules J R}
    (f : L' ⟶ L) (N : Modules J R) :
    ((ordinaryModuleHom J R).map f.op).app N =
      SheafOfModules.homObjMap f (𝟙 N) := by
  exact (internalHomMapApp_eq_pre f N).trans
    (SheafOfModules.pre_app.{u} (C := C) (J := J) (R := R) f N)

private noncomputable def signedOrdinary (I : CochainComplex (Modules J R) ℤ) :
    (CochainComplex (Modules J R) ℤ)ᵒᵖ ⥤ CochainComplex (Modules J R) ℤ where
  obj X := CochainComplex.bifunctorHomObj (ordinaryModuleHom J R) X.unop I
  map f := CochainComplex.bifunctorHomMapLeft f.unop
  map_id _X := CochainComplex.bifunctorHomMapLeft_id
  map_comp f g := CochainComplex.bifunctorHomMapLeft_comp f.unop g.unop

private noncomputable def signIso (L I : CochainComplex (Modules J R) ℤ) :
    ((homComplexFunctor (R := R)).obj (op L)).obj I ≅
      CochainComplex.bifunctorHomObj (ordinaryModuleHom J R) L I :=
  homComplexIsoInternalHomObj L I ≪≫ nativeBifunctorIso L I

@[reassoc]
private theorem signIso_π (L I : CochainComplex (Modules J R) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (signIso J R L I).hom.f n ≫
        CochainComplex.bifunctorHomπ (ordinaryModuleHom J R) L I n p q h =
      (p * n).negOnePow • homComplexIhomπ L I n p q h := by
  change ((homComplexIsoInternalHomObj L I).hom ≫ (nativeBifunctorIso L I).hom).f n ≫
    CochainComplex.bifunctorHomπ MonoidalClosed.internalHom L I n p q h = _
  rw [HomologicalComplex.comp_f, Category.assoc, nativeBifunctorIso_π,
    homComplexIsoInternalHomObj_hom_f_π]

private theorem signNaturality (I : CochainComplex (Modules J R) ℤ)
    {X Y : (CochainComplex (Modules J R) ℤ)ᵒᵖ} (f : X ⟶ Y) :
    ((homComplexFunctor (R := R)).map f).app I ≫ (signIso J R Y.unop I).hom =
      (signIso J R X.unop I).hom ≫ CochainComplex.bifunctorHomMapLeft f.unop := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.bifunctorHomObj_hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc,
    Category.assoc, signIso_π, CochainComplex.bifunctorHomMapLeft_f_π]
  rw [Linear.comp_units_smul, signIso_π_assoc]
  have hmap := homComplexFunctor_map_f_π (R := R) f.unop (𝟙 I) n p q h
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at hmap
  rw [Linear.units_smul_comp]
  apply congrArg (fun t ↦ (p * n).negOnePow • t)
  exact hmap.trans <| congrArg
    (fun g ↦ homComplexπ X.unop I n p q h ≫ g)
    (moduleInternalHomMapApp J R (f.unop.f p) (I.X q)).symm

private noncomputable def signComparison (I : CochainComplex (Modules J R) ℤ) :
    (homComplexFunctor (R := R)).flip.obj I ≅ signedOrdinary J R I :=
  NatIso.ofComponents
    (F := (homComplexFunctor (R := R)).flip.obj I) (G := signedOrdinary J R I)
    (fun X ↦ signIso J R X.unop I) (fun f ↦ signNaturality J R I f)

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]

private noncomputable def complexComparison (I : CochainComplex (Modules J R) ℤ) :
    CochainComplex.bifunctorHomComplexFunctor (ordinaryModuleHom J R) I ≅
      (signedOrdinary J R I ⋙ DerivedCategory.Q).rightOp :=
  NatIso.ofComponents
    (fun X ↦ ((DerivedCategory.quotientCompQhIso (Modules J R)).app _).symm.op) (by
      intro X Y f
      apply Quiver.Hom.unop_inj
      exact (DerivedCategory.quotientCompQhIso_inv_naturality
        (CochainComplex.bifunctorHomMapLeft (H := (ordinaryModuleHom J R))
          (Y := I) f)).symm)

private noncomputable def ordinaryComparison
    (K : CochainComplex (Modules J R) ℤ) :
    DerivedCategory.Q.op ⋙
        (Functor.curry.obj (derivedInternalHom J R)).flip.obj (DerivedCategory.Q.obj K) ≅
      (homComplexFunctor (R := R)).flip.obj
        ((CochainComplex.kInjectiveResolutionFunctor.{u} (Modules J R)).obj K) ⋙
        DerivedCategory.Q := by
  letI : IsGrothendieckAbelian.{u} (Modules J R) := SheafOfModules.isGrothendieckAbelian _
  let e := Classical.choice <| derivedInternalHom_comparison J R
    (CochainComplex.kInjectiveResolutionFunctor.{u} (Modules J R))
    (CochainComplex.toKInjectiveResolution.{u} (Modules J R))
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩)
  exact NatIso.ofComponents (fun X ↦ e.app (X, K)) (by
    intro X Y f
    have h := e.hom.naturality ((f, 𝟙 K) : (X, K) ⟶ (Y, K))
    simpa only [Functor.comp_map, Functor.prod_map, Functor.op_map,
      Functor.id_map, Functor.uncurry_obj_map, Functor.curry_obj_obj_map, Functor.curry_obj_map_app,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj,
      Functor.flip_obj_obj, Functor.curry_obj_obj_obj, Functor.flip_obj_map,
      Iso.app_hom, Functor.map_id, NatTrans.id_app,
      Category.comp_id, Category.id_comp] using h)

private noncomputable def homotopyComparison (M : DerivedCategory (Modules J R)) :
    let K := DerivedCategory.Q.objPreimage M
    let I := (CochainComplex.kInjectiveResolutionFunctor.{u} (Modules J R)).obj K
    (CochainComplex.bifunctorHomHomotopyFunctor (ordinaryModuleHom J R) I).leftOp ≅
      DerivedCategory.Qh.op ⋙ (Functor.curry.obj (derivedInternalHom J R)).flip.obj M := by
  let K := DerivedCategory.Q.objPreimage M
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} (Modules J R)).obj K
  let T := (Functor.curry.obj (derivedInternalHom J R)).flip.obj M
  let eK : DerivedCategory.Q.obj K ≅ M := DerivedCategory.Q.objObjPreimageIso M
  let e : signedOrdinary J R I ⋙ DerivedCategory.Q ≅ DerivedCategory.Q.op ⋙ T :=
    Functor.isoWhiskerRight (signComparison J R I).symm DerivedCategory.Q ≪≫
      (ordinaryComparison J R K).symm ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Q.op
        ((Functor.curry.obj (derivedInternalHom J R)).flip.mapIso eK)
  let F := CochainComplex.bifunctorHomHomotopyFunctor (ordinaryModuleHom J R) I
  let q := HomotopyCategory.quotient (Modules J R) (ComplexShape.up ℤ)
  let eq : q ⋙ F ≅ CochainComplex.bifunctorHomComplexFunctor (ordinaryModuleHom J R) I :=
    CategoryTheory.Quotient.lift.isLift _ _ _
  let pre : q ⋙ F ≅ q ⋙ DerivedCategory.Qh ⋙ T.rightOp :=
    eq ≪≫ complexComparison J R I ≪≫ (rightOpIso e).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (Modules J R)).symm
        T.rightOp
  let eH : F ≅ DerivedCategory.Qh ⋙ T.rightOp :=
    ((Functor.whiskeringLeft _ _ _).obj q).preimageIso pre
  exact Functor.isoWhiskerRight (NatIso.op eH.symm) (CategoryTheory.unopUnop _)

end

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

/-- Contravariant exactness, including the coherent integer shift structure.

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(auxiliary; not a blueprint node).

Proof: Choose a representative K of M and its functorial K-injective replacement I.
Multiplication by (-1)^(p*n) in degree n on the p-th factor identifies the ordinary
Hom complex with the signed bifunctor Hom model, naturally for precomposition.
The localization comparison for RHom identifies this model on the homotopy category
with Qh.op followed by RHom(-,M). Apply the already proved signed bifunctor Hom
exactness theorem. Descend its coherent integer shift structure through Qh.op,
and detect triangulatedness using essential surjectivity on arrows. The construction
keeps the derived universe arbitrary and adds no boundedness or finiteness hypothesis.
-/
theorem ringedInternalHom_contravariant_exact
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] :
    (∀ M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj
    M).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj M).IsTriangulated) := by
  intro M
  let A := Modules J R
  let K := DerivedCategory.Q.objPreimage M
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj K
  let F := (CochainComplex.bifunctorHomHomotopyFunctor (ordinaryModuleHom J R) I).leftOp
  let T := (Functor.curry.obj (derivedInternalHom J R)).flip.obj M
  obtain ⟨sF, hF⟩ :=
    CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact (ordinaryModuleHom J R) I
  let : F.CommShift ℤ := sF
  have : F.IsTriangulated := hF
  let e : F ≅ DerivedCategory.Qh.op ⋙ T := homotopyComparison J R M
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).op
  let : Localization.Lifting DerivedCategory.Qh.op V F T := ⟨e.symm⟩
  let sT := Functor.commShiftOfLocalization DerivedCategory.Qh.op V ℤ F T
  let := sT
  have : NatTrans.CommShift e.inv ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (Localization.Lifting.iso DerivedCategory.Qh.op V F T).hom ℤ)
  have : NatTrans.CommShift e.hom ℤ := by
    constructor
    intro n
    ext X
    dsimp
    rw [← cancel_epi (e.inv.app (X⟦n⟧)), e.inv_hom_id_app_assoc,
      ← NatTrans.shift_app_comm_assoc e.inv, ← Functor.map_comp,
      e.inv_hom_id_app, Functor.map_id, Category.comp_id]
  have : (DerivedCategory.Qh.op ⋙ T).IsTriangulated := Functor.isTriangulated_of_iso e
  have : DerivedCategory.Qh.op.mapArrow.EssSurj :=
    Localization.essSurj_mapArrow DerivedCategory.Qh.op V
  exact ⟨sT, Functor.isTriangulated_of_precomp DerivedCategory.Qh.op T⟩

end CategoryTheory
