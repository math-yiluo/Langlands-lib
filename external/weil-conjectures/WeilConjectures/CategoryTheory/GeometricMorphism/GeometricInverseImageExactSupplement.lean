/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.TraceFormula.AbelianInverseImagePresentation
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exactness of geometric inverse image on abelian sheaves and modules

Source: Stacks Project, Modules on Sites, Tags 04JC, 03D2, 03DA and 03DB;
Sites, Proposition 00YV (2)
(blueprint: lem-trf-geometric-inverse-image-exact).
-/

@[expose] public section

universe w uC vC uD vD

open CategoryTheory.Limits

namespace CategoryTheory.GeometricMorphism

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

private noncomputable abbrev abSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} :=
  hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}

private noncomputable abbrev smallArrowLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (U : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
      AddCommGrpCat.{w} :=
  HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _

attribute [local instance] abSheafify smallArrowLimits

private noncomputable abbrev abLocallyBijective
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
    (A := AddCommGrpCat.{w})

attribute [local instance] abLocallyBijective

private theorem abForgetLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))

attribute [local instance] abForgetLimits

private theorem map_locally_surjective
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (R : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ R)
    {X Y : Sheaf J (Type w)} (g : X ⟶ Y) [Sheaf.IsLocallySurjective g] :
    Sheaf.IsLocallySurjective (L.map g) := by
  constructor
  intro U x
  obtain ⟨S, hS, hs⟩ := Sheaf.map_jointly_locally_surjective L R adj
    (fun _ : Unit ↦ g) (fun V y ↦
      ⟨Presheaf.imageSieve g.hom y, Presheaf.imageSieve_mem J g.hom y,
        fun W a ha ↦ ⟨(), ha⟩⟩) (Opposite.op U) x
  apply K.superset_covering _ hS
  intro V a ha
  obtain ⟨_, y, hy⟩ := hs V a ha
  exact ⟨y, hy⟩

/-- A lift with the prescribed underlying set functor is exact. Kernels are detected
on underlying sheaves; epimorphisms are detected by local surjectivity. -/
private theorem abelian_lift_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {E : Type*} [Category E] [Abelian E]
    (G : E ⥤ Sheaf J AddCommGrpCat.{w})
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (F : E ⥤ Sheaf K AddCommGrpCat.{w})
    (e : F ⋙ sheafCompose K (forget AddCommGrpCat.{w}) ≅
      G ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ⋙ f.inverse) :
    exactFunctor _ _ F := by
  let : PreservesFiniteLimits f.inverse := f.leftExact
  let U := sheafCompose K (forget AddCommGrpCat.{w})
  have : PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ f.inverse) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (G ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ⋙
      f.inverse) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (F ⋙ U) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F U
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have : F.PreservesEpimorphisms := by
    constructor
    intro M N g hg
    have : Sheaf.IsLocallySurjective (G.map g) :=
      (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat.{w} (G.map g)).2
        inferInstance
    have : Sheaf.IsLocallySurjective
        ((sheafCompose J (forget AddCommGrpCat.{w})).map (G.map g)) := inferInstance
    have : Sheaf.IsLocallySurjective
        (f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{w})).map (G.map g))) :=
      map_locally_surjective f.inverse f.direct f.adj _
    have : Sheaf.IsLocallySurjective ((F ⋙ U).map g) := by
      rw [show (F ⋙ U).map g = e.hom.app M ≫
        (G ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ⋙ f.inverse).map g ≫
          e.inv.app N by simpa using e.hom.naturality g =≫ e.inv.app N]
      change Sheaf.IsLocallySurjective (e.hom.app M ≫
        f.inverse.map ((sheafCompose J (forget AddCommGrpCat.{w})).map (G.map g)) ≫
          e.inv.app N)
      infer_instance
    have : Epi ((F ⋙ U).map g) := Sheaf.epi_of_isLocallySurjective' _
    exact U.epi_of_epi_map (show Epi ((F ⋙ U).map g) from inferInstance)
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  rw [exactFunctor_iff]
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology F⟩

/-- Recognize algebra-valued sheaves on an essentially small site without imposing
an inequality between the site universes and the value universe. -/
private theorem sheaf_of_underlying
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {A : Type*} [Category.{w} A]
    [HasLimitsOfSize.{w, w} A] (U : A ⥤ Type w)
    [PreservesLimitsOfSize.{w, w} U] [U.ReflectsIsomorphisms]
    (P : Cᵒᵖ ⥤ A) (h : Presheaf.IsSheaf J (P ⋙ U)) : Presheaf.IsSheaf J P := by
  let e := equivSmallModel.{w} C
  let K := e.inverse.inducedTopology J
  have : ReflectsLimitsOfSize.{w, w} U := reflectsLimits_of_reflectsIsomorphisms
  have hs : Presheaf.IsSheaf K (e.inverse.op ⋙ P) :=
    Presheaf.isSheaf_of_isSheaf_comp K _ U
      (e.inverse.op_comp_isSheaf K J ⟨P ⋙ U, h⟩)
  have hs' := e.functor.op_comp_isSheaf J K ⟨_, hs⟩
  exact (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight e.op.unitIso.symm P)).mp hs'

open CategoryTheory.MonoidalCategory
open SheafOfModules.GeometricConstruction

private def abelianObjects
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{w} ⥤ CommGrp (Sheaf J (Type w)) := by
  let S := sheafCompose J (forget AddCommGrpCat.{w})
  let obj (A : Sheaf J AddCommGrpCat.{w}) : CommGrp (Sheaf J (Type w)) := by
    letI : GrpObj (S.obj A) := {
      one := ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : A.obj.obj U))
                naturality := by intro U V f; ext x; exact (A.obj.map f).hom.map_zero.symm }⟩
      mul := ⟨{ app := fun U ↦ ↾(fun x ↦
                  (show A.obj.obj U from x.1) + (show A.obj.obj U from x.2))
                naturality := by intro U V f; ext x; exact ((A.obj.map f).hom.map_add _ _).symm }⟩
      one_mul := by ext U x; exact zero_add (show A.obj.obj U from x.2)
      mul_one := by ext U x; exact add_zero (show A.obj.obj U from x.1)
      mul_assoc := by ext U x; exact add_assoc (show A.obj.obj U from x.1.1) x.1.2 x.2
      inv := ⟨{ app := fun U ↦ ↾(fun x ↦ -(show A.obj.obj U from x))
                naturality := by intro U V f; ext x; exact ((A.obj.map f).hom.map_neg _).symm }⟩
      left_inv := by ext U x; exact neg_add_cancel (show A.obj.obj U from x)
      right_inv := by ext U x; exact add_neg_cancel (show A.obj.obj U from x) }
    exact { X := S.obj A
            comm := { mul_comm := by ext U x; exact add_comm (show A.obj.obj U from x.2) x.1 } }
  exact {
    obj := obj
    map := fun f ↦ InducedCategory.homMk (Grp.homMk'' (S.map f)
      (by ext U x; exact (f.hom.app U).hom.map_zero)
      (by ext U x; exact (f.hom.app U).hom.map_add _ _)) }

private def groupSheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (G : CommGrp (Sheaf J (Type w))) :
    Sheaf J AddCommGrpCat.{w} := by
  letI (U : Cᵒᵖ) := sectionGroup G U
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{w} := {
    obj U := @AddCommGrpCat.of (G.X.obj.obj U) (sectionGroup G U)
    map {U V} f := by
      letI := sectionGroup G U
      letI := sectionGroup G V
      exact AddCommGrpCat.ofHom {
        toFun := G.X.obj.map f
        map_zero' := (congrArg (fun g ↦ g PUnit.unit)
          ((MonObj.one (X := G.X)).hom.naturality f)).symm
        map_add' := fun a b ↦ (congrArg (fun g ↦ g (a, b))
          ((MonObj.mul (X := G.X)).hom.naturality f)).symm }
    map_id U := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact congrArg (fun g ↦ g x) (G.X.obj.map_id U)
    map_comp f g := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact congrArg (fun h ↦ h x) (G.X.obj.map_comp f g) }
  exact ⟨P, sheaf_of_underlying (forget AddCommGrpCat.{w}) P G.X.property⟩

private def groupSheaves
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : CommGrp (Sheaf J (Type w)) ⥤ Sheaf J AddCommGrpCat.{w} where
  obj := groupSheaf
  map {G H} f := ⟨{
    app U := AddCommGrpCat.ofHom
      (X := (groupSheaf G).obj.obj U) (Y := (groupSheaf H).obj.obj U) {
      toFun := f.hom.hom.hom.hom.app U
      map_zero' := congrArg (fun k ↦ k.hom.app U PUnit.unit)
        (IsMonHom.one_hom f.hom.hom.hom)
      map_add' := fun a b ↦ congrArg (fun k ↦ k.hom.app U (a, b))
        (IsMonHom.mul_hom f.hom.hom.hom) }
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.hom.hom.hom.naturality g) x }⟩

private theorem abelian_presentation_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L] :
    Nonempty (AbelianInverseImagePresentation L) := by
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let F := abelianObjects J ⋙ L.mapCommGrp ⋙ groupSheaves K
  refine ⟨{ functor := F, underlying := Iso.refl _, map_add := ?_, map_zero := ?_ }⟩
  · intro M T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫
        MonObj.mul (X := ((abelianObjects J).obj M).X) := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  · intro M T a ha V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        MonObj.one (X := ((abelianObjects J).obj M).X) := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl

@[instance_reducible] private def ringStructure
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{w}) :
    CommRingObj ((sheafCompose J (forget CommRingCat.{w})).obj A) where
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

-- Sectionwise reconstruction follows `SheafRingObjectReconstruction`, with the
-- sheaf condition checked on a small model to retain independent site universes.
noncomputable section RingReconstruction

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
private abbrev sadd
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a b : R.X.obj.obj U) : R.X.obj.obj U :=
  (AddMonObj.add (X := R.X)).hom.app U (a, b)
private abbrev szero
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : R.X.obj.obj U :=
  (AddMonObj.zero (X := R.X)).hom.app U PUnit.unit
private abbrev sneg
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a : R.X.obj.obj U) : R.X.obj.obj U :=
  (AddGrpObj.neg (X := R.X)).hom.app U a
private abbrev smul
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) (a b : R.X.obj.obj U) : R.X.obj.obj U :=
  (MonObj.mul (X := R.X)).hom.app U (a, b)
private abbrev sone
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : R.X.obj.obj U :=
  (MonObj.one (X := R.X)).hom.app U PUnit.unit

private abbrev sectionAddGroup
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : AddCommGroup (R.X.obj.obj U) where
  add := sadd R U
  zero := szero R U
  neg := sneg R U
  add_assoc a b c := congrArg (fun f => f.hom.app U ((a, b), c))
    (AddMonObj.add_assoc R.X)
  zero_add a := congrArg (fun f => f.hom.app U (PUnit.unit, a))
    (AddMonObj.zero_add R.X)
  add_zero a := congrArg (fun f => f.hom.app U (a, PUnit.unit))
    (AddMonObj.add_zero R.X)
  add_comm a b := (congrArg (fun f => f.hom.app U (a, b))
    (IsCommAddMonObj.add_comm R.X)).symm
  neg_add_cancel a := congrArg (fun f => f.hom.app U a) (AddGrpObj.left_neg R.X)
  nsmul := @nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩
  zsmul := @zsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩ ⟨sneg R U⟩
    (@nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩)

private abbrev sectionMonoid
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : CommMonoid (R.X.obj.obj U) where
  mul := smul R U
  one := sone R U
  mul_assoc a b c := congrArg (fun f => f.hom.app U ((a, b), c))
    (MonObj.mul_assoc R.X)
  one_mul a := congrArg (fun f => f.hom.app U (PUnit.unit, a))
    (MonObj.one_mul R.X)
  mul_one a := congrArg (fun f => f.hom.app U (a, PUnit.unit))
    (MonObj.mul_one R.X)
  mul_comm a b := (congrArg (fun f => f.hom.app U (a, b))
    (IsCommMonObj.mul_comm R.X)).symm

private abbrev sectionCommRing
    (R : CommRingObjCat (Sheaf J (Type w))) (U : Cᵒᵖ) : CommRing (R.X.obj.obj U) := by
  letI := sectionAddGroup R U
  letI := sectionMonoid R U
  exact {
    left_distrib := fun a b c => congrArg (fun f => f.hom.app U (a, (b, c)))
      (RingObj.mul_add R.X)
    right_distrib := fun a b c => congrArg (fun f => f.hom.app U ((a, b), c))
      (RingObj.add_mul R.X)
    mul_zero := by
      intro a
      have h : a * (0 + 0) = a * 0 + a * 0 :=
        congrArg (fun f => f.hom.app U (a, (0, 0))) (RingObj.mul_add R.X)
      simpa using h
    zero_mul := by
      intro a
      have h : (0 + 0) * a = 0 * a + 0 * a :=
        congrArg (fun f => f.hom.app U ((0, 0), a)) (RingObj.add_mul R.X)
      simpa using h }

private def reconstructedPresheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : CommRingObjCat (Sheaf J (Type (w)))) :
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

end RingReconstruction

private def ringSheaf
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : CommRingObjCat (Sheaf J (Type w))) :
    Sheaf J CommRingCat.{w} :=
  ⟨reconstructedPresheaf R,
    sheaf_of_underlying (forget CommRingCat.{w}) _ R.X.property⟩

private def imageRing
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [L.Braided]
    (R : Sheaf J CommRingCat.{w}) : Sheaf K CommRingCat.{w} := by
  let X := (sheafCompose J (forget CommRingCat.{w})).obj R
  letI := ringStructure J R
  letI := Adjunction.transportedRing L X
  exact ringSheaf ⟨L.obj X⟩

private theorem algebraic_presentation_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{w}) :
    ∃ S : Sheaf K CommRingCat.{w}, Nonempty (SheafOfModules.AlgebraicInverseImage L R S) := by
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let S := imageRing L R
  let d : rset S ⟶ L.obj (rset R) := 𝟙 _
  have ha : ringAdd S ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ L _ _ ≫
      L.map (ringAdd R) := by
    simp only [d, Category.comp_id, tensorHom_id]
    rfl
  have hm : letI := ringMonoid R
            letI := ringMonoid S
            letI := L.monObjObj (rset R)
            IsMonHom d := by
    let := ringMonoid R
    let := ringMonoid S
    let := L.monObjObj (rset R)
    constructor
    · simp only [d, Category.comp_id]
    · simp only [d, Category.comp_id, tensorHom_id]
      rfl
  let F := imageFunctor L R S d ha hm
  have hAdd (T : Sheaf J (Type w))
      (a b t : T ⟶ rset R)
      (ht : ∀ U x, t.hom.app U x =
        @Add.add (R.obj.obj U) inferInstance (a.hom.app U x) (b.hom.app U x))
      (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
      (L.map t).hom.app V x =
        @Add.add (S.obj.obj V) inferInstance
          ((L.map a).hom.app V x) ((L.map b).hom.app V x) := by
    have he : t = CartesianMonoidalCategory.lift a b ≫ ringAdd R := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  have hMAdd (M : SheafOfModules.{w} (base R)) (T : Sheaf J (Type w))
      (a b t : T ⟶ (mset R).obj M)
      (ht : ∀ U x, t.hom.app U x =
        @Add.add (M.val.obj U) inferInstance (a.hom.app U x) (b.hom.app U x))
      (V : Dᵒᵖ) (x : (L.obj T).obj.obj V) :
      (L.map t).hom.app V x =
        @Add.add ((F.obj M).val.obj V) inferInstance
          ((L.map a).hom.app V x) ((L.map b).hom.app V x) := by
    have he : t = CartesianMonoidalCategory.lift a b ≫ addition R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  refine ⟨S, ⟨{
    ringUnderlying := Iso.refl _
    ringAdd := hAdd
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    modules := F
    moduleUnderlying := imageFunctorUnderlying L R S d ha hm
    moduleAdd := hMAdd
    moduleZero := ?_
    moduleSMul := ?_ }⟩⟩
  · intro T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫ ringMul R := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  · intro T a ha V x
    let := ringStructure J R
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        AddMonObj.zero (X := rset R) := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro T a ha V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫ ringOne R := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro M T a ha V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        MonObj.one (X := (additiveObject R M).X) := by
      ext U y
      exact ha U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro M T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫ action R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    change _ = (imageAction L R S d M).hom.app V
      ((L.map a).hom.app V x, (L.map b).hom.app V x)
    simp only [imageAction, d, tensorHom_id]
    rfl

private def unliftSetSheafIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} :
    sheafCompose J uliftFunctor.{w, w} ≅ 𝟭 (Sheaf J (Type w)) :=
  NatIso.ofComponents (fun T ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro T T' f; rfl)

-- The same conjugation by `ULift.down` is used in `LocalizationInverseImageCoherence`.
private noncomputable def inverseImageUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R S := by
  let eJ := unliftSetSheafIso (J := J)
  let eK := unliftSetSheafIso (J := K)
  let rR := (sheafCompose J (forget CommRingCat.{w})).obj R
  let rS := (sheafCompose K (forget CommRingCat.{w})).obj S
  let mR := SheafOfModules.toSheaf.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})
  let mS := SheafOfModules.toSheaf.{w}
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) ⋙
      sheafCompose K (forget AddCommGrpCat.{w})
  refine
    { ringUnderlying := L.mapIso (eJ.app rR) ≪≫ a.ringUnderlying ≪≫ (eK.app rS).symm
      modules := a.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft a.modules (Functor.isoWhiskerLeft mS eK) ≪≫
          a.moduleUnderlying ≪≫
            Functor.isoWhiskerRight (Functor.isoWhiskerLeft mR eJ.symm) L
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringAdd T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringMul T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringZero T (x ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringOne T (x ≫ eJ.hom.app rR) h W q
  · intro M T x y z h W q
    have h' := a.moduleAdd M T (x ≫ eJ.hom.app (mR.obj M))
      (y ≫ eJ.hom.app (mR.obj M)) (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T x h W q
    have h' := a.moduleZero M T (x ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T r x z h W q
    have h' := a.moduleSMul M T (r ≫ eJ.hom.app rR) (x ≫ eJ.hom.app (mR.obj M))
      (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl

/-- Geometric inverse image induces exact functors on abelian sheaves and on modules
with transported scalars. The existence clauses supply the transports; the universal
clauses make exactness available for every normalized presentation of them.
Source: Stacks Project, Modules on Sites, 04JC (first assertion), 03D2, 03DA and 03DB;
Sites, 00YV (2) (blueprint: lem-trf-geometric-inverse-image-exact).

Proof, following the five steps of the node:
1. The adjunction and left exactness are `f.adj` and `f.leftExact`. The right adjoint
preserves limits (situation-conventions). Identify abelian sheaves
with commutative group objects (situation-conventions).
The adjunction lifts to those objects (situation-conventions),
with the transported operations and the underlying set-sheaf adjunction. This gives an
abelian presentation, and applies to any presentation by its operation normalization.
2. Finite abelian-sheaf limits are sectionwise (situation-conventions).
Their underlying sets are the same compatible tuples as in set sheaves
(lem-weil-pbc-site-sheaf-sets-limits-sectionwise). Applying `f.inverse` gives a limiting
underlying cone. Its unique factorizations are additive by joint uniqueness of the
projections, applied to addition, zero and negation. Thus abelian inverse image is left exact.
3. The lifted adjunction preserves colimits (situation-conventions),
in particular finite colimits and cokernels. This proves exactness as defined in
`def-galois-exact-functor`. Abelian sheaves are abelian categories
(lem-weil-pbc-site-sheaves-enough-injectives), so preservation of kernels and cokernels
also preserves images and exact sequences. Transported addition makes the functor additive.
4. Apply inverse image to the ring operations and module action through the finite-product
comparisons (03D2). Applying it to each axiom diagram proves all ring and module laws.
Naturality of the action gives linearity on maps. This supplies the algebraic presentation;
its underlying abelian functor is the one of steps 1--3, including its action on maps.
5. Scalar forgetting preserves limits and colimits
(situation-conventions), and reflects isomorphisms: the inverse of
an invertible linear map is linear, sectionwise. The finite-limit and finite-colimit
comparisons for module inverse image become those of step 2 and step 3 after forgetting,
so they are isomorphisms. Hence module inverse image and its underlying-abelian-sheaf
functor are exact, including preservation of relation-map cokernels. The target ring
throughout is the transported ring itself, with no further change of scalars. -/
theorem geometric_inverse_image_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))) :
    (∃ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ B : Sheaf J CommRingCat.{w},
      (∃ (BI : Sheaf K CommRingCat.{w}),
        Nonempty (SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI)) ∧
      ∀ (BI : Sheaf K CommRingCat.{w})
        (I : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI),
        exactFunctor _ _ I.modules ∧
        exactFunctor _ _ (I.modules ⋙ SheafOfModules.toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj BI))) := by
  let : PreservesFiniteLimits f.inverse := f.leftExact
  have hA (A : AbelianInverseImagePresentation f.inverse) : exactFunctor _ _ A.functor :=
    abelian_lift_exact f (𝟭 _) A.functor A.underlying
  obtain ⟨A⟩ := abelian_presentation_exists f.inverse
  refine ⟨⟨A, hA A⟩, hA, ?_⟩
  intro B
  obtain ⟨BI, ⟨I⟩⟩ := algebraic_presentation_exists f.inverse B
  refine ⟨⟨BI, ⟨inverseImageUniverses (L := f.inverse) (R := B) (S := BI) I⟩⟩, ?_⟩
  intro BI I
  let R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B
  let S := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj BI
  let U := SheafOfModules.toSheaf R
  let V := SheafOfModules.toSheaf S
  have : PreservesFiniteLimits U := (moduleSheaves_colimits_forgetful R).2.1
  have : PreservesFiniteColimits U := (moduleSheaves_colimits_forgetful R).2.2.1
  have : PreservesFiniteLimits V := (moduleSheaves_colimits_forgetful S).2.1
  have : PreservesFiniteColimits V := (moduleSheaves_colimits_forgetful S).2.2.1
  let eJ := Functor.isoWhiskerLeft (sheafCompose J (forget AddCommGrpCat.{w}))
    (unliftSetSheafIso (J := J))
  let eK := Functor.isoWhiskerLeft (sheafCompose K (forget AddCommGrpCat.{w}))
    (unliftSetSheafIso (J := K))
  let e : (I.modules ⋙ V) ⋙ sheafCompose K (forget AddCommGrpCat.{w}) ≅
      U ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ⋙ f.inverse :=
    Functor.isoWhiskerLeft I.modules (Functor.isoWhiskerLeft V eK.symm) ≪≫
      I.moduleUnderlying ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft U eJ) f.inverse
  have h := abelian_lift_exact f U (I.modules ⋙ V) e
  have : PreservesFiniteLimits (I.modules ⋙ V) := (exactFunctor_iff _).mp h |>.1
  have : PreservesFiniteColimits (I.modules ⋙ V) := (exactFunctor_iff _).mp h |>.2
  refine ⟨?_, h⟩
  rw [exactFunctor_iff]
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves I.modules V,
    preservesFiniteColimits_of_reflects_of_preserves I.modules V⟩

end CategoryTheory.GeometricMorphism
