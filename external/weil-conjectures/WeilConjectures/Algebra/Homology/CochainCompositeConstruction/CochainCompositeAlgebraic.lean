/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
/-! # Algebraic inverse image of a composite geometric morphism

Source: Stacks Project, Modules on Sites, Tags 03D7 and 0D6D.
(blueprint: lem-pur-independent-composite-algebraic-image).

Finite-product transport constructs the ring and module structures. The graph
laws of the two coefficient maps construct the composite coefficient morphism.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules.CochainCompositeConstruction
attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The five operations of a ring sheaf, with all diagrams checked on sections. -/
@[instance_reducible] private def ringStructure
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{w}) :
    CommRingObj ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj A) where
  zero := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : A.obj.obj U))
             naturality := by
               intro X Y f
               ext x
               change (0 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_zero _).symm }⟩
  add := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 + x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 + (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 + x.2)
              exact (map_add _ _ _).symm }⟩
  neg := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U ↦ -x)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X at x
              change -(A.obj.map f).hom x = (A.obj.map f).hom (-x)
              exact (map_neg _ _).symm }⟩
  one := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : A.obj.obj U))
            naturality := by
               intro X Y f
               ext x
               change (1 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_one _).symm }⟩
  mul := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 * x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 * (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 * x.2)
              exact (map_mul _ _ _).symm }⟩
  zero_add := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (0 : A.obj.obj U) + x.2 = x.2
    exact zero_add x.2
  add_zero := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) + 0 = x.1
    exact add_zero x.1
  add_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) + x.1.2 + x.2 = x.1.1 + (x.1.2 + x.2)
    exact add_assoc x.1.1 x.1.2 x.2
  left_neg := by
    ext U x
    change A.obj.obj U at x
    change -(x : A.obj.obj U) + x = 0
    exact neg_add_cancel x
  right_neg := by
    ext U x
    change A.obj.obj U at x
    change (x : A.obj.obj U) + -x = 0
    exact add_neg_cancel x
  add_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) + x.1 = x.1 + x.2
    exact add_comm x.2 x.1
  one_mul := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (1 : A.obj.obj U) * x.2 = x.2
    exact one_mul x.2
  mul_one := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) * 1 = x.1
    exact mul_one x.1
  mul_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) * x.1.2 * x.2 = x.1.1 * (x.1.2 * x.2)
    exact mul_assoc x.1.1 x.1.2 x.2
  mul_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) * x.1 = x.1 * x.2
    exact mul_comm x.2 x.1
  mul_add := by
    ext U x
    change A.obj.obj U × (A.obj.obj U × A.obj.obj U) at x
    change (x.1 : A.obj.obj U) * (x.2.1 + x.2.2) = x.1 * x.2.1 + x.1 * x.2.2
    exact mul_add x.1 x.2.1 x.2.2
  add_mul := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change ((x.1.1 : A.obj.obj U) + x.1.2) * x.2 = x.1.1 * x.2 + x.1.2 * x.2
    exact add_mul x.1.1 x.1.2 x.2

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
private abbrev sadd (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a b :
    R.X.obj.obj U) :
    R.X.obj.obj U :=
  (AddMonObj.add (X := R.X)).hom.app U (a, b)
private abbrev szero (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : R.X.obj.obj U :=
  (AddMonObj.zero (X := R.X)).hom.app U PUnit.unit
private abbrev sneg (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a :
    R.X.obj.obj U) :
    R.X.obj.obj U :=
  (AddGrpObj.neg (X := R.X)).hom.app U a
private abbrev smul (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a b :
    R.X.obj.obj U) :
    R.X.obj.obj U :=
  (MonObj.mul (X := R.X)).hom.app U (a, b)
private abbrev sone (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : R.X.obj.obj U :=
  (MonObj.one (X := R.X)).hom.app U PUnit.unit

private abbrev sectionAddGroup (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) :
    AddCommGroup (R.X.obj.obj U) where
  add := sadd R U
  zero := szero R U
  neg := sneg R U
  add_assoc a b c := congrArg (fun f ↦ f.hom.app U ((a, b), c))
    (AddMonObj.add_assoc R.X)
  zero_add a := congrArg (fun f ↦ f.hom.app U (PUnit.unit, a))
    (AddMonObj.zero_add R.X)
  add_zero a := congrArg (fun f ↦ f.hom.app U (a, PUnit.unit))
    (AddMonObj.add_zero R.X)
  add_comm a b := (congrArg (fun f ↦ f.hom.app U (a, b))
    (IsCommAddMonObj.add_comm R.X)).symm
  neg_add_cancel a := congrArg (fun f ↦ f.hom.app U a) (AddGrpObj.left_neg R.X)
  nsmul := @nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩
  zsmul := @zsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩ ⟨sneg R U⟩
    (@nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩)

private abbrev sectionMonoid (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) :
    CommMonoid (R.X.obj.obj U) where
  mul := smul R U
  one := sone R U
  mul_assoc a b c := congrArg (fun f ↦ f.hom.app U ((a, b), c))
    (MonObj.mul_assoc R.X)
  one_mul a := congrArg (fun f ↦ f.hom.app U (PUnit.unit, a))
    (MonObj.one_mul R.X)
  mul_one a := congrArg (fun f ↦ f.hom.app U (a, PUnit.unit))
    (MonObj.mul_one R.X)
  mul_comm a b := (congrArg (fun f ↦ f.hom.app U (a, b))
    (IsCommMonObj.mul_comm R.X)).symm

private abbrev sectionCommRing (R :
    CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) :
    CommRing (R.X.obj.obj U) := by
  letI := sectionAddGroup R U
  letI := sectionMonoid R U
  exact {
    left_distrib := fun a b c ↦ congrArg (fun f ↦ f.hom.app U (a, (b, c)))
      (RingObj.mul_add R.X)
    right_distrib := fun a b c ↦ congrArg (fun f ↦ f.hom.app U ((a, b), c))
      (RingObj.add_mul R.X)
    mul_zero := by
      intro a
      have h : a * (0 + 0) = a * 0 + a * 0 :=
        congrArg (fun f ↦ f.hom.app U (a, (0, 0))) (RingObj.mul_add R.X)
      simpa using h
    zero_mul := by
      intro a
      have h : (0 + 0) * a = 0 * a + 0 * a :=
        congrArg (fun f ↦ f.hom.app U ((0, 0), a)) (RingObj.add_mul R.X)
      simpa using h }

private def reconstructedPresheaf
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : CommRingObjCat (Sheaf J (Type w))) :
    Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := @CommRingCat.of (R.X.obj.obj U) (sectionCommRing R U)
  map {U V} f := by
    letI := sectionCommRing R U
    letI := sectionCommRing R V
    exact CommRingCat.ofHom {
      toFun := R.X.obj.map f
      map_zero' := (congrArg (fun g => g PUnit.unit)
        ((AddMonObj.zero (X := R.X)).hom.naturality f)).symm
      map_one' := (congrArg (fun g => g PUnit.unit)
        ((MonObj.one (X := R.X)).hom.naturality f)).symm
      map_add' := fun a b => (congrArg (fun g => g (a, b))
        ((AddMonObj.add (X := R.X)).hom.naturality f)).symm
      map_mul' := fun a b => (congrArg (fun g => g (a, b))
        ((MonObj.mul (X := R.X)).hom.naturality f)).symm }
  map_id U := by
    ext x
    exact congrArg (fun g => g x) (R.X.obj.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun k => k x) (R.X.obj.map_comp f g)

private theorem reconstructed_isSheaf
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : CommRingObjCat (Sheaf J (Type w))) :
    Presheaf.IsSheaf J (reconstructedPresheaf R) := by
  let e := equivSmallModel C
  let K := e.inverse.inducedTopology J
  have hP : Presheaf.IsSheaf K (e.inverse.op ⋙ reconstructedPresheaf R) := by
    let : ReflectsLimitsOfSize.{w, w} (CategoryTheory.forget CommRingCat.{w}) :=
      reflectsLimits_of_reflectsIsomorphisms
    apply Presheaf.isSheaf_of_isSheaf_comp K _ (CategoryTheory.forget CommRingCat.{w})
    change Presheaf.IsSheaf K (e.inverse.op ⋙ R.X.obj)
    exact e.inverse.op_comp_isSheaf K J R.X
  have h := e.functor.op_comp_isSheaf J K
    (show Sheaf K CommRingCat.{w} from ⟨_, hP⟩)
  exact (Presheaf.isSheaf_of_iso_iff
    (Functor.isoWhiskerRight e.op.unitIso.symm (reconstructedPresheaf R))).mp h

private noncomputable def reconstructedSheaf
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : CommRingObjCat (Sheaf J (Type w))) :
    Sheaf J CommRingCat.{w} := ⟨reconstructedPresheaf R, reconstructed_isSheaf R⟩

universe uD vD
variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {K : GrothendieckTopology D}

private noncomputable def ringImage
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    (A : Sheaf J CommRingCat.{w}) : Sheaf K CommRingCat.{w} := by
  let X : CommRingObjCat (Sheaf J (Type w)) :=
    { X := (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj A
      commRingObj := ringStructure J A }
  let : CommRingObj X.X := X.commRingObj
  let Y : CommRingObjCat (Sheaf K (Type w)) :=
    { X := F.obj X.X
      commRingObj := CategoryTheory.Adjunction.transportedRing F X.X }
  exact reconstructedSheaf Y

open SheafOfModules.GeometricConstruction
private noncomputable def ringImageUnderlying
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    (A : Sheaf J CommRingCat.{w}) : rset (ringImage F A) ≅ F.obj (rset A) := Iso.refl _

private theorem ringImage_add
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    (A : Sheaf J CommRingCat.{w}) :
    ringAdd (ringImage F A) ≫ (ringImageUnderlying F A).hom =
      ((ringImageUnderlying F A).hom ⊗ₘ (ringImageUnderlying F A).hom) ≫
        Functor.LaxMonoidal.μ F _ _ ≫ F.map (ringAdd A) := by
  simp only [ringImageUnderlying, Iso.refl_hom, id_tensorHom_id, Category.comp_id,
    Category.id_comp]
  rfl

private theorem ringImage_mul
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    (A : Sheaf J CommRingCat.{w}) :
    ringMul (ringImage F A) ≫ (ringImageUnderlying F A).hom =
      ((ringImageUnderlying F A).hom ⊗ₘ (ringImageUnderlying F A).hom) ≫
        Functor.LaxMonoidal.μ F _ _ ≫ F.map (ringMul A) := by
  simp only [ringImageUnderlying, Iso.refl_hom, id_tensorHom_id, Category.comp_id,
    Category.id_comp]
  rfl

private theorem graph_binary
    {C D : Type*} [Category C] [Category D] [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) {X Y Z T : C} {A B E : D}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (h : F.map a = prodComparison F X Y ≫ prod.map eX.inv eY.inv ≫ b ≫ eZ.hom)
    (x : T ⟶ X) (y : T ⟶ Y) (t : T ⟶ Z) (ht : t = prod.lift x y ≫ a) :
    F.map t ≫ eZ.inv = prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv) ≫ b := by
  have hp : F.map (prod.lift x y) ≫ prodComparison F X Y =
      prod.lift (F.map x) (F.map y) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← F.map_comp, prod.lift_fst]
    · simp only [Category.assoc, prodComparison_snd, ← F.map_comp, prod.lift_snd]
  rw [ht, F.map_comp, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, hp]
  rw [prod.lift_map]

private theorem graph_sections
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {X Y Z T : Sheaf J (Type w)} {A B E : Sheaf K (Type w)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (h : F.map a = prodComparison F X Y ≫ prod.map eX.inv eY.inv ≫ b ≫ eZ.hom)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p) ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p) ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z)
    (hz : ∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) :
    ∀ V p, (F.map z ≫ eZ.inv).hom.app V p =
      op' V ((F.map x ≫ eX.inv).hom.app V p)
        ((F.map y ≫ eY.inv).hom.app V p) := by
  have he : z = prod.lift x y ≫ a := by
    ext U p
    change z.hom.app U p = a.hom.app U ((prod.lift x y).hom.app U p)
    rw [hs, hz]
    have h₁ := congrArg (fun k : T ⟶ X ↦ k.hom.app U p) (prod.lift_fst x y)
    have h₂ := congrArg (fun k : T ⟶ Y ↦ k.hom.app U p) (prod.lift_snd x y)
    change (prod.fst : X ⨯ Y ⟶ X).hom.app U ((prod.lift x y).hom.app U p) = _ at h₁
    change (prod.snd : X ⨯ Y ⟶ Y).hom.app U ((prod.lift x y).hom.app U p) = _ at h₂
    rw [h₁, h₂]
  have he' := graph_binary F eX eY eZ a b h x y z he
  intro V p
  have hh := congrArg (fun k ↦ k.hom.app V p) he'
  change (F.map z ≫ eZ.inv).hom.app V p =
    b.hom.app V ((prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv)).hom.app V p) at hh
  rw [ht] at hh
  have h₁ := congrArg (fun k : F.obj T ⟶ A ↦ k.hom.app V p)
    (prod.lift_fst (F.map x ≫ eX.inv) (F.map y ≫ eY.inv))
  have h₂ := congrArg (fun k : F.obj T ⟶ B ↦ k.hom.app V p)
    (prod.lift_snd (F.map x ≫ eX.inv) (F.map y ≫ eY.inv))
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv)).hom.app V p) = _ at h₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv)).hom.app V p) = _ at h₂
  rw [h₁, h₂] at hh
  exact hh

private theorem ringImage_graph_add
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    (A : Sheaf J CommRingCat.{w}) (Z : Sheaf J (Type w))
    (a b t : Z ⟶ rset A)
    (ht : ∀ U x, @Eq (A.obj.obj U) (t.hom.app U x)
      (@Add.add (A.obj.obj U) inferInstance
        (a.hom.app U x) (b.hom.app U x))) :
    ∀ V x, @Eq ((ringImage F A).obj.obj V)
      ((F.map t ≫ (ringImageUnderlying F A).inv).hom.app V x)
      (@Add.add ((ringImage F A).obj.obj V) inferInstance
        ((F.map a ≫ (ringImageUnderlying F A).inv).hom.app V x)
        ((F.map b ≫ (ringImageUnderlying F A).inv).hom.app V x)) := by
  let e := ringImageUnderlying F A
  have h : F.map (fromProd _ _ ≫ ringAdd A) =
      prodComparison F _ _ ≫ prod.map e.inv e.inv ≫
        (fromProd _ _ ≫ ringAdd (ringImage F A)) ≫ e.hom := by
    apply (binary_transport_iff F _ _ e _ _).2
    exact ringImage_add F A
  exact graph_sections F e e e (fromProd _ _ ≫ ringAdd A)
    (fromProd _ _ ≫ ringAdd (ringImage F A)) h
    (fun U x y ↦ @Add.add (A.obj.obj U) inferInstance x y)
    (fun V x y ↦ @Add.add ((ringImage F A).obj.obj V) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a b t ht

private theorem ringImage_graph_mul
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    (A : Sheaf J CommRingCat.{w}) (Z : Sheaf J (Type w))
    (a b t : Z ⟶ rset A)
    (ht : ∀ U x, @Eq (A.obj.obj U) (t.hom.app U x)
      (@Mul.mul (A.obj.obj U) inferInstance
        (a.hom.app U x) (b.hom.app U x))) :
    ∀ V x, @Eq ((ringImage F A).obj.obj V)
      ((F.map t ≫ (ringImageUnderlying F A).inv).hom.app V x)
      (@Mul.mul ((ringImage F A).obj.obj V) inferInstance
        ((F.map a ≫ (ringImageUnderlying F A).inv).hom.app V x)
        ((F.map b ≫ (ringImageUnderlying F A).inv).hom.app V x)) := by
  let e := ringImageUnderlying F A
  have h : F.map (fromProd _ _ ≫ ringMul A) =
      prodComparison F _ _ ≫ prod.map e.inv e.inv ≫
        (fromProd _ _ ≫ ringMul (ringImage F A)) ≫ e.hom := by
    apply (binary_transport_iff F _ _ e _ _).2
    exact ringImage_mul F A
  exact graph_sections F e e e (fromProd _ _ ≫ ringMul A)
    (fromProd _ _ ≫ ringMul (ringImage F A)) h
    (fun U x y ↦ @Mul.mul (A.obj.obj U) inferInstance x y)
    (fun V x y ↦ @Mul.mul ((ringImage F A).obj.obj V) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a b t ht

private noncomputable def algebraicImage
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [F.Braided]
    [PreservesFiniteLimits F] (R : Sheaf J CommRingCat.{w}) :
    AlgebraicInverseImage F R (ringImage F R) := by
  let RI := ringImage F R
  let eR := ringImageUnderlying F R
  have haI := ringImage_add F R
  have hmI := ringIso_isMonHom F R RI eR (ringImage_mul F R)
  let I := imageFunctor F R RI eR.hom haI hmI
  let eI := imageFunctorUnderlying F R RI eR.hom haI hmI
  have hAdd := ringImage_graph_add F R
  have hMul := ringImage_graph_mul F R
  refine {
    ringUnderlying := eR.symm
    ringAdd := fun T x y z hz ↦ hAdd T x y z hz
    ringMul := fun T x y z hz ↦ hMul T x y z hz
    ringZero := ?_
    ringOne := ?_
    modules := I
    moduleUnderlying := eI
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }
  · intro T z hz U x
    have h := hAdd T z z z (by
      intro W t
      have hz' : @Eq (R.obj.obj W) (z.hom.app W t) 0 := hz W t
      exact hz'.trans ((zero_add (0 : R.obj.obj W)).symm.trans
        (congrArg₂ (fun a b : R.obj.obj W ↦ a + b) hz'.symm hz'.symm))) U x
    exact add_eq_left.mp h.symm
  · intro T z hz U x
    let S := (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj R
    let X := T ⨯ S
    let q := sectionPair (F.obj T) (F.obj S) U x
      (eR.hom.hom.app U (1 : RI.obj.obj U))
    let p := (inv (prodComparison F T S)).hom.app U q
    have h₁ : inv (prodComparison F T S) ≫ F.map (prod.fst : X ⟶ T) = prod.fst := by
      rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
    have h₂ : inv (prodComparison F T S) ≫ F.map (prod.snd : X ⟶ S) = prod.snd := by
      rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
    have hp₁ : (F.map (prod.fst : X ⟶ T)).hom.app U p = x := by
      change (inv (prodComparison F T S) ≫ F.map (prod.fst : X ⟶ T)).hom.app U q = x
      rw [h₁]
      exact sectionPair_fst _ _ _ _ _
    have hp₂ : (F.map (prod.snd : X ⟶ S)).hom.app U p =
        eR.hom.hom.app U (1 : RI.obj.obj U) := by
      change (inv (prodComparison F T S) ≫ F.map (prod.snd : X ⟶ S)).hom.app U q = _
      rw [h₂]
      exact sectionPair_snd _ _ _ _ _
    have he := hMul X (prod.fst ≫ z) prod.snd prod.snd (by
      intro W t
      have hz' : @Eq (R.obj.obj W) (z.hom.app W ((prod.fst : X ⟶ T).hom.app W t)) 1 :=
        hz W _
      change (prod.snd : X ⟶ S).hom.app W t =
        @Mul.mul (R.obj.obj W) inferInstance
          (z.hom.app W ((prod.fst : X ⟶ T).hom.app W t))
          ((prod.snd : X ⟶ S).hom.app W t)
      exact (one_mul (show R.obj.obj W from (prod.snd : X ⟶ S).hom.app W t)).symm.trans
        (congrArg (fun a : R.obj.obj W ↦ a *
          (show R.obj.obj W from (prod.snd : X ⟶ S).hom.app W t)) hz'.symm)) U p
    rw [F.map_comp] at he
    change eR.inv.hom.app U ((F.map (prod.snd : X ⟶ S)).hom.app U p) =
      @Mul.mul (RI.obj.obj U) inferInstance
        (eR.inv.hom.app U ((F.map z).hom.app U
          ((F.map (prod.fst : X ⟶ T)).hom.app U p)))
        (eR.inv.hom.app U ((F.map (prod.snd : X ⟶ S)).hom.app U p)) at he
    rw [hp₁, hp₂] at he
    have hi := congrArg (fun k ↦ k.hom.app U (1 : RI.obj.obj U)) eR.hom_inv_id
    change eR.inv.hom.app U (eR.hom.hom.app U (1 : RI.obj.obj U)) =
      (1 : RI.obj.obj U) at hi
    let v : RI.obj.obj U := eR.inv.hom.app U ((F.map z).hom.app U x)
    exact (mul_one v).symm.trans
      ((congrArg (fun b : RI.obj.obj U ↦ v * b) hi.symm).trans (he.symm.trans hi))
  · intro M T a b t ht
    let addM := fromProd _ _ ≫ addition R M
    let muM := fromProd _ _ ≫ action R M
    let addI := fromProd _ _ ≫ addition RI (I.obj M)
    let muI := fromProd _ _ ≫ action RI (I.obj M)
    have heaI : F.map addM = prodComparison F _ _ ≫
        prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M := by
      change F.map (fromProd _ _ ≫ addition R M) = prodComparison F _ _ ≫
        prod.map (𝟙 _) (𝟙 _) ≫ (fromProd _ _ ≫
          addition RI (imageModule F R RI eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [prod.map_id_id, Category.id_comp, Category.comp_id]
      exact imageModule_addition_comparison F R RI eR.hom haI hmI M
    have hesI : F.map muM = prodComparison F _ _ ≫
        prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M := by
      change F.map (fromProd _ _ ≫ action R M) = prodComparison F _ _ ≫
        prod.map eR.inv (𝟙 _) ≫ (fromProd _ _ ≫
          action RI (imageModule F R RI eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [Category.comp_id]
      exact imageModule_action_comparison F R RI eR haI hmI M
    exact graph_sections F (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.obj M).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a b t ht
  · intro M T a ha U x
    let addM := fromProd _ _ ≫ addition R M
    let muM := fromProd _ _ ≫ action R M
    let addI := fromProd _ _ ≫ addition RI (I.obj M)
    let muI := fromProd _ _ ≫ action RI (I.obj M)
    have heaI : F.map addM = prodComparison F _ _ ≫
        prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M := by
      change F.map (fromProd _ _ ≫ addition R M) = prodComparison F _ _ ≫
        prod.map (𝟙 _) (𝟙 _) ≫ (fromProd _ _ ≫
          addition RI (imageModule F R RI eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [prod.map_id_id, Category.id_comp, Category.comp_id]
      exact imageModule_addition_comparison F R RI eR.hom haI hmI M
    have hesI : F.map muM = prodComparison F _ _ ≫
        prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M := by
      change F.map (fromProd _ _ ≫ action R M) = prodComparison F _ _ ≫
        prod.map eR.inv (𝟙 _) ≫ (fromProd _ _ ≫
          action RI (imageModule F R RI eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [Category.comp_id]
      exact imageModule_action_comparison F R RI eR haI hmI M
    have h := graph_sections F (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.obj M).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a a a
      (by
        intro W t
        have ha' : @Eq (M.val.obj W) (a.hom.app W t) 0 := ha W t
        exact ha'.trans ((zero_add (0 : M.val.obj W)).symm.trans
          (congrArg₂ (fun a b : M.val.obj W ↦ a + b) ha'.symm ha'.symm))) U x
    exact add_eq_left.mp h.symm
  · intro M T a b t ht
    let addM := fromProd _ _ ≫ addition R M
    let muM := fromProd _ _ ≫ action R M
    let addI := fromProd _ _ ≫ addition RI (I.obj M)
    let muI := fromProd _ _ ≫ action RI (I.obj M)
    have heaI : F.map addM = prodComparison F _ _ ≫
        prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M := by
      change F.map (fromProd _ _ ≫ addition R M) = prodComparison F _ _ ≫
        prod.map (𝟙 _) (𝟙 _) ≫ (fromProd _ _ ≫
          addition RI (imageModule F R RI eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [prod.map_id_id, Category.id_comp, Category.comp_id]
      exact imageModule_addition_comparison F R RI eR.hom haI hmI M
    have hesI : F.map muM = prodComparison F _ _ ≫
        prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M := by
      change F.map (fromProd _ _ ≫ action R M) = prodComparison F _ _ ≫
        prod.map eR.inv (𝟙 _) ≫ (fromProd _ _ ≫
          action RI (imageModule F R RI eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [Category.comp_id]
      exact imageModule_action_comparison F R RI eR haI hmI M
    exact graph_sections F eR (eI.app M) (eI.app M) muM muI hesI
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.obj M).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a b t ht

private theorem reflect_binary
    {C D : Type*} [Category C] [Category D] [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) [PreservesFiniteProducts F]
    {X : C} {A B : D} (e : A ≅ F.obj X)
    (a : X ⨯ X ⟶ X) (b : A ⨯ A ⟶ A) (c : B ⨯ B ⟶ B) (φ : F.obj X ⟶ B)
    (h : F.map a = prodComparison F X X ≫ prod.map e.inv e.inv ≫ b ≫ e.hom)
    (hφ : F.map a ≫ φ = prodComparison F X X ≫ prod.map φ φ ≫ c) :
    b ≫ e.hom ≫ φ = prod.map (e.hom ≫ φ) (e.hom ≫ φ) ≫ c := by
  apply (cancel_epi (prodComparison F X X ≫ prod.map e.inv e.inv)).mp
  have hh := (congrArg (fun k ↦ k ≫ φ) h).symm.trans hφ
  simpa only [Category.assoc, prod.map_map_assoc, Iso.inv_hom_id_assoc] using hh

private theorem binary_of_graph
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {X Y Z : Sheaf J (Type w)} {A B E : Sheaf K (Type w)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type w)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private theorem binary_hom_sections
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    {X Y Z A B E : Sheaf J (Type w)}
    (dX : X ⟶ A) (dY : Y ⟶ B) (dZ : Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ U, A.obj.obj U → B.obj.obj U → E.obj.obj U)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ U p, b.hom.app U p =
      op' U ((prod.fst : A ⨯ B ⟶ A).hom.app U p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app U p))
    (h : a ≫ dZ = prod.map dX dY ≫ b) :
    ∀ U x y, dZ.hom.app U (op U x y) =
      op' U (dX.hom.app U x) (dY.hom.app U y) := by
  intro U x y
  let p := SheafOfModules.sectionPair X Y U x y
  have hh := congrArg (fun k ↦ k.hom.app U p) h
  change dZ.hom.app U (a.hom.app U p) = b.hom.app U ((prod.map dX dY).hom.app U p) at hh
  rw [hs, ht] at hh
  rw [SheafOfModules.prodMap_fst_apply, SheafOfModules.prodMap_snd_apply] at hh
  simpa only [p, SheafOfModules.sectionPair_fst, SheafOfModules.sectionPair_snd] using hh

open SheafOfModules.GeometricConstruction

private noncomputable abbrev radd
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable abbrev rmul
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) := fromProd (rset R) (rset R) ≫ ringMul R

private theorem structuralMap
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits F]
    (B : Sheaf J CommRingCat.{w}) (A : Sheaf K CommRingCat.{w})
    (RI : Sheaf K CommRingCat.{w}) (I : AlgebraicInverseImage F B RI)
    (φ : F.obj (rset B) ⟶ rset A)
    (hadd : ∀ (Z : Sheaf J (Type w)) (x y z : Z ⟶ rset B),
      (∀ U t, @Eq (B.obj.obj U) (z.hom.app U t)
        (@Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t))) →
      ∀ U t, @Eq (A.obj.obj U) ((F.map z ≫ φ).hom.app U t)
        (@Add.add (A.obj.obj U) inferInstance
          ((F.map x ≫ φ).hom.app U t) ((F.map y ≫ φ).hom.app U t)))
    (hmul : ∀ (Z : Sheaf J (Type w)) (x y z : Z ⟶ rset B),
      (∀ U t, @Eq (B.obj.obj U) (z.hom.app U t)
        (@Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t))) →
      ∀ U t, @Eq (A.obj.obj U) ((F.map z ≫ φ).hom.app U t)
        (@Mul.mul (A.obj.obj U) inferInstance
          ((F.map x ≫ φ).hom.app U t) ((F.map y ≫ φ).hom.app U t)))
    (hone : ∀ (Z : Sheaf J (Type w)) (z : Z ⟶ rset B),
      (∀ U t, @Eq (B.obj.obj U) (z.hom.app U t) 1) →
      ∀ U t, @Eq (A.obj.obj U) ((F.map z ≫ φ).hom.app U t) 1) :
    ∃ c : RI ⟶ A, (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map c =
      I.ringUnderlying.inv ≫ φ := by
  let e := I.ringUnderlying.symm
  let d := e.hom ≫ φ
  have hca : F.map (radd B) ≫ e.inv =
      prodComparison F (rset B) (rset B) ≫ prod.map e.inv e.inv ≫ radd RI :=
    binary_of_graph F e.inv e.inv e.inv (radd B) (radd RI)
      (fun U x y ↦ @Add.add (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) I.ringAdd
  have hcm : F.map (rmul B) ≫ e.inv =
      prodComparison F (rset B) (rset B) ≫ prod.map e.inv e.inv ≫ rmul RI :=
    binary_of_graph F e.inv e.inv e.inv (rmul B) (rmul RI)
      (fun U x y ↦ @Mul.mul (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) I.ringMul
  have ha : F.map (radd B) =
      prodComparison F (rset B) (rset B) ≫
        prod.map e.inv e.inv ≫ radd RI ≫ e.hom := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hca
  have hm : F.map (rmul B) =
      prodComparison F (rset B) (rset B) ≫
        prod.map e.inv e.inv ≫ rmul RI ≫ e.hom := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hcm
  have hφa : F.map (radd B) ≫ φ =
      prodComparison F (rset B) (rset B) ≫ prod.map φ φ ≫ radd A :=
    binary_of_graph F φ φ φ (radd B) (radd A)
      (fun U x y ↦ @Add.add (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (A.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hadd
  have hφm : F.map (rmul B) ≫ φ =
      prodComparison F (rset B) (rset B) ≫ prod.map φ φ ≫ rmul A :=
    binary_of_graph F φ φ φ (rmul B) (rmul A)
      (fun U x y ↦ @Mul.mul (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (A.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hmul
  have hAdd := binary_hom_sections d d d (radd RI) (radd A)
    (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (A.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (reflect_binary F e (radd B) (radd RI) (radd A) φ ha hφa)
  have hMul := binary_hom_sections d d d (rmul RI) (rmul A)
    (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Mul.mul (A.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (reflect_binary F e (rmul B) (rmul RI) (rmul A) φ hm hφm)
  have hOne (U : Dᵒᵖ) : d.hom.app U (1 : RI.obj.obj U) = (1 : A.obj.obj U) := by
    let z : rset B ⟶ rset B := CartesianMonoidalCategory.toUnit _ ≫ ringOne B
    let p := e.hom.hom.app U (1 : RI.obj.obj U)
    have hi := I.ringOne (rset B) z (fun _ _ ↦ rfl) U p
    have hf := hone (rset B) z (fun _ _ ↦ rfl) U p
    have hi' : (F.map z).hom.app U p = p := by
      apply (ConcreteCategory.bijective_of_isIso (e.inv.hom.app U)).injective
      exact hi.trans (congrArg (fun k ↦ k.hom.app U (1 : RI.obj.obj U)) e.hom_inv_id).symm
    change φ.hom.app U p = (1 : A.obj.obj U)
    change φ.hom.app U ((F.map z).hom.app U p) = _ at hf
    rw [hi'] at hf
    exact hf
  have hZero (U : Dᵒᵖ) : d.hom.app U (0 : RI.obj.obj U) = (0 : A.obj.obj U) := by
    have h := hAdd U (0 : RI.obj.obj U) (0 : RI.obj.obj U)
    have hh := (congrArg (fun x : RI.obj.obj U ↦ d.hom.app U x)
      (zero_add (0 : RI.obj.obj U))).symm.trans h
    exact (@add_eq_left (A.obj.obj U) inferInstance inferInstance _ _).mp hh.symm
  refine ⟨⟨{
    app := fun U ↦ CommRingCat.ofHom {
      toFun := d.hom.app U
      map_one' := hOne U
      map_mul' := hMul U
      map_zero' := hZero U
      map_add' := hAdd U }
    naturality := ?_
  }⟩, rfl⟩
  intro U V i
  ext x
  exact CategoryTheory.congr_fun (d.hom.naturality i) x

universe uE vE
variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {H : GrothendieckTopology E}
  [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

attribute [local irreducible] ringImage algebraicImage

-- Prevent accidental unfolding of the transported ring structures during elaboration.
end SheafOfModules.CochainCompositeConstruction
