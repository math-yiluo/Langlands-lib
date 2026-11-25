/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option linter.privateModule false

/-!
# Flat internal module sheaves under a site inverse image

The algebraic comparison argument of `SectionModuleAlgebraicInverseImage` only
uses continuity and representable flatness of the underlying site functor. We
carry it out for general sites here, without changing the scheme-specific API.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
namespace CategoryTheory.SiteInverseImageModuleFlat

set_option autoImplicit false
set_option synthInstance.maxSize 4096

private structure Site where
  C : Type (u + 1)
  [category : Category.{u} C]
  J : GrothendieckTopology C
  [sheafifyAb : HasSheafify J Ab.{u + 1}]
  [monoidalAb : (J.W (A := Ab.{u + 1})).IsMonoidal]
  [sheafifyType : HasSheafify J (Type (u + 1))]
  [locallyBijectiveAb : J.WEqualsLocallyBijective Ab.{u + 1}]

attribute [instance] Site.category Site.sheafifyAb Site.monoidalAb Site.sheafifyType
  Site.locallyBijectiveAb
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private structure Pullback (X Y : Site.{u}) where
  base : Y.C ⥤ X.C
  [continuous : base.IsContinuous Y.J X.J]
  [flat : RepresentablyFlat base]

attribute [instance] Pullback.continuous Pullback.flat

private abbrev abelianPullback {X Y : Site.{u}} (f : Pullback X Y) :=
  Functor.sheafPullbackConstruction.sheafPullback f.base Ab.{u + 1} Y.J X.J

private abbrev abelianPushforward {X Y : Site.{u}} (f : Pullback X Y) :=
  f.base.sheafPushforwardContinuous Ab.{u + 1} Y.J X.J

private abbrev abelianAdjunction {X Y : Site.{u}} (f : Pullback X Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f.base Ab.{u + 1} Y.J X.J

/- The concrete inverse image and its comparison after forgetting abelian groups. -/
private noncomputable def setPullback {X Y : Site.{u}} (f : Pullback X Y) :
    Sheaf Y.J (Type (u + 1)) ⥤
      Sheaf X.J (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    f.base (Type (u + 1))
    Y.J X.J
private noncomputable def pullbackForgetIso {X Y : Site.{u}} (f : Pullback X Y) :
    (abelianPullback f) ⋙ sheafCompose X.J
        (CategoryTheory.forget Ab.{u + 1}) ≅
      sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1}) ⋙
        setPullback f := by
  let U := f.base
  let G := CategoryTheory.forget Ab.{u + 1}
  have (P : Y.Cᵒᵖ ⥤ Ab.{u + 1}) :
      G.PreservesPointwiseLeftKanExtension P U.op := fun W ↦ by
    have : IsFiltered (CostructuredArrow U.op W) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
    have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
      have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
      have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
      infer_instance
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W
  let eLan := G.lanCompIsoOfPreserves U.op
  let eSh := sheafComposeNatIso X.J G
    (sheafificationAdjunction _ Ab.{u + 1})
    (sheafificationAdjunction _ (Type (u + 1)))
  exact Functor.isoWhiskerLeft
      (sheafToPresheaf Y.J Ab.{u + 1} ⋙ U.op.lan) eSh.symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf Y.J Ab.{u + 1})
      (Functor.isoWhiskerRight eLan
        (presheafToSheaf X.J (Type (u + 1))))

/- Concrete coefficient and module comparisons, including the universe lifts. -/
private noncomputable def sheafUliftIso
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A : Type*} [Category A] (G : A ⥤ Type (u + 1))
    [J.HasSheafCompose G] [J.HasSheafCompose (G ⋙ uliftFunctor.{u + 1, u + 1})] :
    sheafCompose J (G ⋙ uliftFunctor.{u + 1, u + 1}) ≅ sheafCompose J G :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun W ↦ uliftTrivial (G.obj (M.obj.obj W)))
      (by intros; rfl))) (by intros; rfl)

private noncomputable def sectionRingUnderlyingIso {X : Site.{u}}
    (R : Sheaf X.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (sheafCompose X.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J R) ≅
    (sheafCompose X.J (CategoryTheory.forget Ab.{u + 1})).obj R :=
  (sheafUliftIso X.J (CategoryTheory.forget CommRingCat.{u + 1})).app _

private noncomputable def sectionRingPullbackIso {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    let L := setPullback f
    L.obj ((sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        Y.J R)) ≅
    (sheafCompose X.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S) :=
  (setPullback f).mapIso (sectionRingUnderlyingIso R) ≪≫
    ((pullbackForgetIso f).app R).symm ≪≫
    (sheafCompose X.J
      (CategoryTheory.forget Ab.{u + 1})).mapIso (asIso ρ).symm ≪≫
    (sectionRingUnderlyingIso S).symm

private noncomputable def sectionModulePullbackIso {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      Y.J R
    let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      X.J S
    (eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor) ⋙ SheafOfModules.toSheaf _ ⋙
      sheafCompose X.J
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1}) ≅
    (SheafOfModules.toSheaf _ ⋙ sheafCompose Y.J
      (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})) ⋙ setPullback f := by
  dsimp only
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    Y.J R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    X.J S
  let I := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
  let UX := sheafCompose X.J (CategoryTheory.forget Ab.{u + 1})
  let UY := sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})
  let RY := (sheafCompose Y.J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        Y.J R)
  let F := SheafOfModules.toSheaf RY ⋙ UY
  let euX := sheafUliftIso X.J (CategoryTheory.forget Ab.{u + 1})
  let euY := sheafUliftIso Y.J (CategoryTheory.forget Ab.{u + 1})
  let e₁ : I ⋙ SheafOfModules.toSheaf _ ⋙ UX ≅
      eY.inverse ⋙ Mod.forget R ⋙ UY ⋙ setPullback f :=
    Functor.isoWhiskerLeft (eY.inverse ⋙ Mod.forget R) (pullbackForgetIso f)
  let e₂ : eY.inverse ⋙ Mod.forget R ⋙ UY ≅ F :=
    Functor.isoWhiskerRight eY.counitIso F
  exact Functor.isoWhiskerLeft (I ⋙ SheafOfModules.toSheaf _) euX ≪≫
    e₁ ≪≫ Functor.isoWhiskerRight e₂ (setPullback f) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.toSheaf _) euY.symm) (setPullback f)

private theorem sectionModulePullbackIso_inv_factor {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      Y.J R
    let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      X.J S
    let I := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
    let QY := SheafOfModules.toSheaf ((sheafCompose Y.J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        Y.J R))
    let QX := SheafOfModules.toSheaf ((sheafCompose X.J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S))
    let UY := sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})
    let euY := sheafUliftIso Y.J (CategoryTheory.forget Ab.{u + 1})
    let euX := sheafUliftIso X.J (CategoryTheory.forget Ab.{u + 1})
    ∀ M, (sectionModulePullbackIso f R S ρ).inv.app M =
      (setPullback f).map ((euY.app (QY.obj M)).hom ≫
        (QY ⋙ UY).map (eY.counitIso.inv.app M)) ≫
      (pullbackForgetIso f).inv.app (eY.inverse.obj M).X ≫
      (euX.app (QX.obj (I.obj M))).inv := by
  intro eY eX I QY QX UY euY euX M
  rw [Functor.map_comp]
  dsimp only [sectionModulePullbackIso]
  simp only [Category.assoc]
  rfl

private theorem sectionModulePullbackIso_inv_apply {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      Y.J R
    let QY := SheafOfModules.toSheaf ((sheafCompose Y.J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        Y.J R))
    let UY := sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})
    let euY := sheafUliftIso Y.J (CategoryTheory.forget Ab.{u + 1})
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose Y.J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R)))
      (T : Sheaf Y.J (Type (u + 1)))
      (q : T ⟶ (QY ⋙ sheafCompose Y.J
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M)
      (V : X.Cᵒᵖ) (x : ((setPullback f).obj T).obj.obj V),
    (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app V
      (((setPullback f).map q).hom.app V x)).down =
      (((setPullback f).map (q ≫ (euY.app (QY.obj M)).hom ≫
          (QY ⋙ UY).map (eY.counitIso.inv.app M)) ≫
        (pullbackForgetIso f).inv.app (eY.inverse.obj M).X).hom.app V x) := by
  intro eY QY UY euY M T q V x
  rw [sectionModulePullbackIso_inv_factor]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/- Compatibility with the two adjunction units. -/
private theorem setPullback_unit_hom {X Y : Site.{u}} (f : Pullback X Y)
    (G : Sheaf Y.J (Type (u + 1))) :
    let U := f.base
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) Y.J X.J).unit.app G).hom =
      U.op.leftKanExtensionUnit G.obj ≫ Functor.whiskerLeft U.op
        (toSheafify X.J (U.op.leftKanExtension G.obj)) := by
  dsimp only
  let U := f.base
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction (Type (u + 1))).comp
      (sheafificationAdjunction X.J (Type (u + 1))))
    (fullyFaithfulSheafToPresheaf Y.J (Type (u + 1)))
    (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback U
      (Type (u + 1)) Y.J X.J)
    (R := U.sheafPushforwardContinuous (Type (u + 1))
      Y.J X.J)
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h
private theorem abelianPullback_unit_hom {X Y : Site.{u}} (f : Pullback X Y)
    (G : Sheaf Y.J Ab.{u + 1}) :
    let U := f.base
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      Ab.{u + 1} Y.J X.J).unit.app G).hom =
      U.op.leftKanExtensionUnit G.obj ≫ Functor.whiskerLeft U.op
        (toSheafify X.J (U.op.leftKanExtension G.obj)) := by
  dsimp only
  let U := f.base
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction Ab.{u + 1}).comp
      (sheafificationAdjunction X.J Ab.{u + 1}))
    (fullyFaithfulSheafToPresheaf Y.J Ab.{u + 1})
    (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback U
      Ab.{u + 1} Y.J X.J)
    (R := U.sheafPushforwardContinuous Ab.{u + 1}
      Y.J X.J)
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h

private theorem pullbackForgetIso_unit_hom {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) :
    let U := f.base
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) Y.J X.J).unit.app
        ((sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})).obj R)).hom ≫
      Functor.whiskerLeft U.op ((pullbackForgetIso f).inv.app R).hom =
    Functor.whiskerRight ((abelianAdjunction f).unit.app R).hom
      (CategoryTheory.forget Ab.{u + 1}) := by
  let U := f.base
  let G := CategoryTheory.forget Ab.{u + 1}
  have (P : Y.Cᵒᵖ ⥤ Ab.{u + 1}) :
      G.PreservesPointwiseLeftKanExtension P U.op := fun W ↦ by
    have : IsFiltered (CostructuredArrow U.op W) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
    have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
      have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
      have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
      infer_instance
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W
  dsimp only
  rw [setPullback_unit_hom]
  dsimp only [pullbackForgetIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, ObjectProperty.FullSubcategory.comp_hom]
  simp only [← Functor.whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  erw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
  simp only [Functor.associator]
  rw [Category.assoc, ← Functor.whiskerLeft_comp]
  erw [sheafComposeNatTrans_fac]
  erw [abelianPullback_unit_hom f R]
  ext W x
  rfl

/- The additive operation graphs follow by transposition through the set adjunction. -/
private noncomputable def sumSections {X : Site.{u}}
    {T : Sheaf X.J (Type (u + 1))}
    (A : Sheaf X.J Ab.{u + 1})
    (a b : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ (@id (A.obj.obj W) (a.hom.app W x)) +
       (@id (A.obj.obj W) (b.hom.app W x)))
     naturality := fun V W q ↦ by
       ext x
       change _ = (A.obj.map q).hom (_ + _)
       exact (congrArg₂ (fun (a b : A.obj.obj W) ↦ a + b)
         (ConcreteCategory.congr_hom (a.hom.naturality q) x)
         (ConcreteCategory.congr_hom (b.hom.naturality q) x)).trans
         (map_add (A.obj.map q).hom _ _).symm }⟩

private theorem pullback_add_graph {X Y : Site.{u}} (f : Pullback X Y)
    (A : Sheaf Y.J Ab.{u + 1})
    (T : Sheaf Y.J (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A)
    (h : ∀ W x, t.hom.app W x = (@id (A.obj.obj W) (a.hom.app W x)) +
      (@id (A.obj.obj W) (b.hom.app W x))) :
    (setPullback f).map t ≫ (pullbackForgetIso f).inv.app A =
      sumSections ((abelianPullback f).obj A)
        ((setPullback f).map a ≫ (pullbackForgetIso f).inv.app A)
        ((setPullback f).map b ≫ (pullbackForgetIso f).inv.app A) := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  have he : (adj.homEquiv _ _ ((pullbackForgetIso f).inv.app A)).hom =
      Functor.whiskerRight ((abelianAdjunction f).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := pullbackForgetIso_unit_hom f A
  have hq (q : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A) :
      (adj.homEquiv _ _ ((setPullback f).map q ≫
        (pullbackForgetIso f).inv.app A)).hom =
      q.hom ≫ Functor.whiskerRight
        ((abelianAdjunction f).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := by
    erw [adj.homEquiv_naturality_left]
    exact congrArg (fun z ↦ q.hom ≫ z) he
  apply ObjectProperty.hom_ext _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  ext W x
  have ha := ConcreteCategory.congr_hom (NatTrans.congr_app (hq a) W) x
  have hb := ConcreteCategory.congr_hom (NatTrans.congr_app (hq b) W) x
  change ((abelianAdjunction f).unit.app A).hom.app W
      (t.hom.app W x) = _
  rw [h W x, map_add]
  change _ = (@id (((abelianPullback f).obj A).obj.obj (U.op.obj W))
    (((pullbackForgetIso f).inv.app A).hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W) ((adj.unit.app T).hom.app W x)))) +
    (@id (((abelianPullback f).obj A).obj.obj (U.op.obj W))
    (((pullbackForgetIso f).inv.app A).hom.app (U.op.obj W)
      (((setPullback f).map b).hom.app (U.op.obj W) ((adj.unit.app T).hom.app W x))))
  exact congrArg₂ (fun (a b : ((abelianPullback f).obj A).obj.obj (U.op.obj W)) ↦ a + b)
    ha.symm hb.symm
private noncomputable def zeroSections {X : Site.{u}}
    (T : Sheaf X.J (Type (u + 1)))
    (A : Sheaf X.J Ab.{u + 1}) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (0 : A.obj.obj W))
     naturality := fun V W q ↦ by
       ext x
       exact (map_zero (A.obj.map q).hom).symm }⟩

private theorem pullback_zero_graph {X Y : Site.{u}} (f : Pullback X Y)
    (A : Sheaf Y.J Ab.{u + 1})
    (T : Sheaf Y.J (Type (u + 1)))
    (a : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A)
    (h : ∀ W x, a.hom.app W x = (0 : A.obj.obj W)) :
    (setPullback f).map a ≫ (pullbackForgetIso f).inv.app A =
      zeroSections ((setPullback f).obj T) ((abelianPullback f).obj A) := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  have he : (adj.homEquiv _ _ ((pullbackForgetIso f).inv.app A)).hom =
      Functor.whiskerRight ((abelianAdjunction f).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := pullbackForgetIso_unit_hom f A
  apply ObjectProperty.hom_ext _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  ext W x
  change ((abelianAdjunction f).unit.app A).hom.app W
      (a.hom.app W x) = (0 : ((abelianPullback f).obj A).obj.obj (U.op.obj W))
  rw [h W x, map_zero]

/- Pointwise ring and action formulas for pushforward and its adjunction unit. -/
private theorem section_mul {X : Site.{u}}
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : X.Cᵒᵖ) (a b : S.obj.obj W) :
    let RX := (InternalAbelianSheafModule.sectionRings X.J S).obj W
    @HMul.hMul RX RX RX inferInstance a b =
      (μ[S]).hom.app W ((Functor.LaxMonoidal.μ
        (sheafToPresheaf X.J Ab.{u + 1}) S S).app W
          (a ⊗ₜ[ℤ] b)) := rfl

private theorem section_one {X : Site.{u}}
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : X.Cᵒᵖ) :
    let RX := (InternalAbelianSheafModule.sectionRings X.J S).obj W
    (1 : RX) = (η[S]).hom.app W ((Functor.LaxMonoidal.ε
      (sheafToPresheaf X.J Ab.{u + 1})).app W (ULift.up 1)) := rfl

private theorem pushforward_section_mul {X Y : Site.{u}} (f : Pullback X Y)
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Y.Cᵒᵖ)
    (a b : S.obj.obj (f.base.op.obj W)) :
    let RY := (InternalAbelianSheafModule.sectionRings Y.J
      ((abelianPushforward f).obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings X.J S).obj
      (f.base.op.obj W)
    @HMul.hMul RY RY RY inferInstance a b =
      @HMul.hMul RX RX RX inferInstance a b := by
  let U := f.base
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    U Ab.{u + 1} Y.J X.J S S W
  refine (section_mul ((abelianPushforward f).obj S) W a b).trans
    ((Eq.trans ?_ (section_mul S (U.op.obj W) a b).symm))
  have hmul : μ[((abelianPushforward f).obj S)] =
      Functor.LaxMonoidal.μ ((abelianPushforward f)) S S ≫
        ((abelianPushforward f)).map μ[S] := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf Y.J Ab.{u + 1}).map hmul) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
  have ht' := congrArg (fun x : (S ⊗ S).obj.obj (U.op.obj W) ↦
    (μ[S]).hom.app (U.op.obj W) x) ht
  exact ht'

private theorem pushforward_section_one {X Y : Site.{u}} (f : Pullback X Y)
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Y.Cᵒᵖ) :
    let RY := (InternalAbelianSheafModule.sectionRings Y.J
      ((abelianPushforward f).obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings X.J S).obj
      (f.base.op.obj W)
    @OfNat.ofNat RY 1 inferInstance = @OfNat.ofNat RX 1 inferInstance := by
  let U := f.base
  have h := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    U Ab.{u + 1} Y.J X.J W
  refine (section_one ((abelianPushforward f).obj S) W).trans
    ((Eq.trans ?_ (section_one S (U.op.obj W)).symm))
  have hunit : η[((abelianPushforward f).obj S)] =
      Functor.LaxMonoidal.ε ((abelianPushforward f)) ≫
        ((abelianPushforward f)).map η[S] := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf Y.J Ab.{u + 1}).map hunit) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (ULift.up 1)
  have ht' := congrArg (fun x : (𝟙_ (Sheaf X.J Ab.{u + 1})).obj.obj
      (U.op.obj W) ↦ (η[S]).hom.app (U.op.obj W) x) ht
  exact ht'
private theorem section_smul {X : Site.{u}}
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (M : Mod (Sheaf X.J Ab.{u + 1}) S)
    (W : X.Cᵒᵖ) (a : S.obj.obj W) (b : M.X.obj.obj W) :
    let RX := (InternalAbelianSheafModule.sectionRings X.J S).obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      X.J S).obj M).val.obj W
    @HSMul.hSMul RX MX MX inferInstance a b =
      (Mod.act M.X).hom.app W ((Functor.LaxMonoidal.μ
        (sheafToPresheaf X.J Ab.{u + 1}) S M.X).app W
          (a ⊗ₜ[ℤ] b)) := rfl

private theorem pushforward_section_smul {X Y : Site.{u}} (f : Pullback X Y)
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (M : Mod (Sheaf X.J Ab.{u + 1}) S)
    (W : Y.Cᵒᵖ)
    (a : S.obj.obj (f.base.op.obj W))
    (b : M.X.obj.obj (f.base.op.obj W)) :
    let RY := (InternalAbelianSheafModule.sectionRings Y.J
      ((abelianPushforward f).obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings X.J S).obj
      (f.base.op.obj W)
    let MY := ((InternalAbelianSheafModule.sectionModuleFunctor
      Y.J ((abelianPushforward f).obj S)).obj
        ((((abelianPushforward f)).mapMod S).obj M)).val.obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      X.J S).obj M).val.obj
        (f.base.op.obj W)
    @HSMul.hSMul RY MY MY inferInstance a b =
      @HSMul.hSMul RX MX MX inferInstance a b := by
  let U := f.base
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    U Ab.{u + 1} Y.J X.J S M.X W
  refine (section_smul _ ((((abelianPushforward f)).mapMod S).obj M) W a b).trans
    ((Eq.trans ?_ (section_smul S M (U.op.obj W) a b).symm))
  have hact : Mod.act (((((abelianPushforward f)).mapMod S).obj M).X) =
      Functor.LaxMonoidal.μ ((abelianPushforward f)) S M.X ≫
        ((abelianPushforward f)).map (Mod.act M.X) := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf Y.J Ab.{u + 1}).map hact) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
  have ht' := congrArg (fun x : (S ⊗ M.X).obj.obj (U.op.obj W) ↦
    (Mod.act M.X).hom.app (U.op.obj W) x) ht
  exact ht'
private theorem section_comap_smul {X : Site.{u}}
    (R S : Sheaf X.J Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod (Sheaf X.J Ab.{u + 1}) S)
    (W : X.Cᵒᵖ) (a : R.obj.obj W) (b : M.X.obj.obj W) :
    let RR := (InternalAbelianSheafModule.sectionRings X.J R).obj W
    let RS := (InternalAbelianSheafModule.sectionRings X.J S).obj W
    let MR := ((InternalAbelianSheafModule.sectionModuleFunctor
      X.J R).obj ((Mod.comap φ).obj M)).val.obj W
    let MS := ((InternalAbelianSheafModule.sectionModuleFunctor
      X.J S).obj M).val.obj W
    @HSMul.hSMul RR MR MR inferInstance a b =
      @HSMul.hSMul RS MS MS inferInstance (φ.hom.app W a) b := by
  let H := sheafToPresheaf X.J Ab.{u + 1}
  have he : Functor.LaxMonoidal.μ H R M.X ≫
      H.map (Mod.act ((Mod.comap φ).obj M).X) =
      H.map φ ▷ H.obj M.X ≫ Functor.LaxMonoidal.μ H S M.X ≫ H.map (Mod.act M.X) := by
    change _ ≫ H.map (φ ▷ M.X ≫ Mod.act M.X) = _
    rw [Functor.map_comp, Functor.LaxMonoidal.μ_natural_left_assoc]
  have ht := ConcreteCategory.congr_hom (NatTrans.congr_app he W) (a ⊗ₜ[ℤ] b)
  change (Mod.act ((Mod.comap φ).obj M).X).hom.app W
      ((Functor.LaxMonoidal.μ H R M.X).app W (a ⊗ₜ[ℤ] b)) =
    (Mod.act M.X).hom.app W ((Functor.LaxMonoidal.μ H S M.X).app W
      ((φ.hom.app W ▷ M.X.obj.obj W) (a ⊗ₜ[ℤ] b))) at ht
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul] at ht
  exact ht

private noncomputable def sectionRingMap {X : Site.{u}}
    {R S : Sheaf X.J Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (g : R ⟶ S) [IsMonHom g] (W : X.Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings X.J R).obj W →+*
      (InternalAbelianSheafModule.sectionRings X.J S).obj W := by
  let H := (sheafToPresheaf X.J Ab.{u + 1}).mapCommMon ⋙
    (Monoidal.commMonFunctorCategoryEquivalence X.Cᵒᵖ Ab.{u + 1}).functor
  exact InternalAbelianSheafModule.ringHom
    ((H.map (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) ⟨g⟩)).app W).hom.hom

private noncomputable def pushforwardSectionRingHom {X Y : Site.{u}} (f : Pullback X Y)
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Y.Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings Y.J
      ((abelianPushforward f).obj S)).obj W →+*
    (InternalAbelianSheafModule.sectionRings X.J S).obj
      (f.base.op.obj W) where
  toFun := fun a ↦ a
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := pushforward_section_one f S W
  map_mul' a b := pushforward_section_mul f S W a b

private noncomputable def inverseImageSectionRingUnit {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (W : Y.Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings Y.J R).obj W →+*
    (InternalAbelianSheafModule.sectionRings X.J S).obj
      (f.base.op.obj W) :=
by
  haveI : IsMonHom ((abelianAdjunction f).unit.app R) :=
    (abelianAdjunction f).isMonHom_unitAlgHom R
  haveI : IsMonHom (asIso ρ).inv := inferInstance
  haveI : IsMonHom (((abelianPushforward f)).map (asIso ρ).inv) :=
    Functor.map.instIsMonHom (F := (abelianPushforward f)) _ _ (asIso ρ).inv
  exact (pushforwardSectionRingHom f S W).comp
    (sectionRingMap ((abelianAdjunction f).unit.app R ≫
      ((abelianPushforward f)).map (asIso ρ).inv) W)

private theorem sectionModuleCounit_smul {Y : Site.{u}}
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      Y.J R
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose Y.J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R)))
      (W : Y.Cᵒᵖ)
      (a : (InternalAbelianSheafModule.sectionRings Y.J R).obj W)
      (b : M.val.obj W),
    let RR := (InternalAbelianSheafModule.sectionRings Y.J R).obj W
    let NM := ((InternalAbelianSheafModule.sectionModuleFunctor
      Y.J R).obj (eY.inverse.obj M)).val.obj W
    ((eY.counitIso.inv.app M).val.app W).hom (a • b) =
      @HSMul.hSMul RR NM NM inferInstance a
        (((eY.counitIso.inv.app M).val.app W).hom b) := by
  intro eY M W a b
  exact ((eY.counitIso.inv.app M).val.app W).hom.map_smul a b

/-- Commutativity of a monoid object transports along an isomorphism of monoid objects. -/
private theorem isCommMonObj_of_isIso {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {M N : C} [MonObj M] [IsCommMonObj M] [MonObj N]
    (ρ : M ⟶ N) [IsIso ρ] [IsMonHom ρ] : IsCommMonObj N where
  mul_comm := by
    have h : μ[N] = (inv ρ ⊗ₘ inv ρ) ≫ μ[M] ≫ ρ := by
      rw [← IsMonHom.mul_hom_assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [h, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

private theorem inverseImageSectionModuleUnit_smul {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (N : Mod (Sheaf Y.J Ab.{u + 1}) R)
    (W : Y.Cᵒᵖ) (a : R.obj.obj W) (b : N.X.obj.obj W) :
    let U := f.base
    let RY := (InternalAbelianSheafModule.sectionRings Y.J R).obj W
    let SX := (InternalAbelianSheafModule.sectionRings X.J S).obj
      (U.op.obj W)
    let MY := ((InternalAbelianSheafModule.sectionModuleFunctor
      Y.J R).obj N).val.obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      X.J S).obj ((Mod.mapModComap ρ).obj N)).val.obj (U.op.obj W)
    ((abelianAdjunction f).unit.app N.X).hom.app W
      (@HSMul.hSMul RY MY MY inferInstance a b) =
      @HSMul.hSMul SX MX MX inferInstance (inverseImageSectionRingUnit f R S ρ W a)
        (((abelianAdjunction f).unit.app N.X).hom.app W b) := by
  have := isCommMonObj_of_isIso ρ
  let U := f.base
  let adj := abelianAdjunction f
  let P := (((abelianPullback f)).mapMod R).obj N
  let Z := (((abelianPushforward f)).mapMod ((abelianPullback f).obj R)).obj P
  let j := (adj.mapModAdjunction R).unit.app N
  let H := InternalAbelianSheafModule.sectionModuleFunctor Y.J R
  have hj := (((H.map j).val.app W).hom).map_smul
    (show (InternalAbelianSheafModule.sectionRings Y.J R).obj W from a)
    (show (H.obj N).val.obj W from b)
  have hc := section_comap_smul R ((abelianPushforward f).obj
      ((abelianPullback f).obj R)) (adj.unitAlgHom R) Z W a
      (j.hom.hom.app W b)
  have hp := pushforward_section_smul f ((abelianPullback f).obj R) P W
    ((adj.unit.app R).hom.app W a) (j.hom.hom.app W b)
  have hd := section_comap_smul S ((abelianPullback f).obj R) ρ P (U.op.obj W)
    (inverseImageSectionRingUnit f R S ρ W a) (j.hom.hom.app W b)
  have hr : ρ.hom.app (U.op.obj W) (inverseImageSectionRingUnit f R S ρ W a) =
      (adj.unit.app R).hom.app W a := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun z ↦ z.hom) (asIso ρ).inv_hom_id) (U.op.obj W))
        ((adj.unit.app R).hom.app W a)
    exact he
  rw [hr] at hd
  have hu : j.hom = adj.unit.app N.X := adj.mapModAdjunction_unit_app_hom R N
  have he := hj.trans (hc.trans (hp.trans hd.symm))
  change j.hom.hom.app W _ = _ at he
  rw [hu] at he
  exact he

private theorem sectionRingPullbackIso_unit {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (W : Y.Cᵒᵖ) (r : ULift.{u + 1} (R.obj.obj W)) :
    let U := f.base
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) Y.J X.J
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      ((adj.unit.app ((sheafCompose Y.J
        (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            Y.J R))).hom.app W r)).down =
        inverseImageSectionRingUnit f R S ρ W r.down := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf Y.J
      (Type (u + 1))).map (adj.unit.naturality (sectionRingUnderlyingIso R).hom)) W) r
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackForgetIso_unit_hom f R) W) r.down
  have hn' := congrArg (fun x ↦ ((pullbackForgetIso f).inv.app R).hom.app
    (U.op.obj W) x) hn
  exact congrArg (fun x ↦ ((asIso ρ).inv.hom.app (U.op.obj W)) x) (hn'.symm.trans hu)

/- Ring operation graphs, proved by transposition through the set adjunction. -/
private noncomputable def ringMulSections {X : Site.{u}}
    (R : Sheaf X.J CommRingCat.{u + 1})
    (T : Sheaf X.J (Type (u + 1)))
    (a b : T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ ULift.up
       ((@id (R.obj.obj W) (a.hom.app W x).down) *
         (@id (R.obj.obj W) (b.hom.app W x).down)))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       change _ = (R.obj.map q).hom (_ * _)
       exact (congrArg₂ (fun (a b : R.obj.obj W) ↦ a * b)
         (congrArg ULift.down (ConcreteCategory.congr_hom (a.hom.naturality q) x))
         (congrArg ULift.down (ConcreteCategory.congr_hom (b.hom.naturality q) x))).trans
         (map_mul (R.obj.map q).hom _ _).symm }⟩
private noncomputable def moduleSMulSections {X : Site.{u}}
    (R : Sheaf X.J CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose X.J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (T : Sheaf X.J (Type (u + 1)))
    (a : T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R)
    (b : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj ((SheafOfModules.toSheaf _).obj M)) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj ((SheafOfModules.toSheaf _).obj M) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ ULift.up
       ((@id (R.obj.obj W) (a.hom.app W x).down) •
         (@id (M.val.obj W) (b.hom.app W x).down)))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       change _ = M.val.map q (_ • _)
       exact (congrArg₂ (fun (a : R.obj.obj W) (b : M.val.obj W) ↦ a • b)
         (congrArg ULift.down (ConcreteCategory.congr_hom (a.hom.naturality q) x))
         (congrArg ULift.down (ConcreteCategory.congr_hom (b.hom.naturality q) x))).trans
         (M.val.map_smul q _ _).symm }⟩

private theorem sectionModulePullbackIso_transpose {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      Y.J R
    let QY := SheafOfModules.toSheaf ((sheafCompose Y.J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        Y.J R))
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose Y.J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R)))
      (T : Sheaf Y.J (Type (u + 1)))
      (q : T ⟶ (QY ⋙ sheafCompose Y.J
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M)
      (W : Y.Cᵒᵖ) (x : T.obj.obj W),
    let U := f.base
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) Y.J X.J
    (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app (U.op.obj W)
      (((setPullback f).map q).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      ((abelianAdjunction f).unit.app (eY.inverse.obj M).X).hom.app W
        (((eY.counitIso.inv.app M).val.app W).hom (q.hom.app W x).down) := by
  intro eY QY M T q W x U adj
  let UY := sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})
  let euY := sheafUliftIso Y.J (CategoryTheory.forget Ab.{u + 1})
  let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
  let N := eY.inverse.obj M
  have ht :
      (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app (U.op.obj W)
        (((setPullback f).map q).hom.app (U.op.obj W)
          ((adj.unit.app T).hom.app W x))).down =
      (((setPullback f).map (q ≫ k) ≫
        (pullbackForgetIso f).inv.app N.X).hom.app (U.op.obj W)
          ((adj.unit.app T).hom.app W x)) := by
    exact sectionModulePullbackIso_inv_apply f R S ρ M T q (U.op.obj W)
      ((adj.unit.app T).hom.app W x)
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf Y.J
      (Type (u + 1))).map (adj.unit.naturality (q ≫ k))) W) x
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackForgetIso_unit_hom f N.X) W) ((q ≫ k).hom.app W x)
  have hn' := congrArg (fun z ↦ ((pullbackForgetIso f).inv.app N.X).hom.app
    (U.op.obj W) z) hn
  exact ht.trans (hn'.symm.trans hu)

private theorem sectionRingPullbackIso_transpose {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf Y.J (Type (u + 1)))
    (q : T ⟶ (sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R)) (W : Y.Cᵒᵖ) (x : T.obj.obj W) :
    let U := f.base
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) Y.J X.J
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map q).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      inverseImageSectionRingUnit f R S ρ W (q.hom.app W x).down := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf Y.J
      (Type (u + 1))).map (adj.unit.naturality q)) W) x
  have hn' := congrArg (fun z ↦
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W) z).down) hn
  exact hn'.symm.trans (sectionRingPullbackIso_unit f R S ρ W (q.hom.app W x))
private theorem sectionRingPullback_mul_graph {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf Y.J (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R))
    (h : ∀ W x, (t.hom.app W x).down =
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        Y.J R).obj W)
        (a.hom.app W x).down) *
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        Y.J R).obj W)
        (b.hom.app W x).down)) :
    (setPullback f).map t ≫ (sectionRingPullbackIso f R S ρ).hom =
      ringMulSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S)
        ((setPullback f).obj T)
        ((setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom)
        ((setPullback f).map b ≫ (sectionRingPullbackIso f R S ρ).hom) := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map t).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down = _
  erw [sectionRingPullbackIso_transpose]
  change _ = (@id ((InternalAbelianSheafModule.sectionRings
      X.J S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down) *
    (@id ((InternalAbelianSheafModule.sectionRings
      X.J S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map b).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down)
  erw [sectionRingPullbackIso_transpose, sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit f R S ρ W) (h W x)).trans
    (map_mul (inverseImageSectionRingUnit f R S ρ W) _ _)
private noncomputable def ringAddSections {X : Site.{u}}
    (R : Sheaf X.J CommRingCat.{u + 1})
    (T : Sheaf X.J (Type (u + 1)))
    (a b : T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ ULift.up
       ((@id (R.obj.obj W) (a.hom.app W x).down) +
         (@id (R.obj.obj W) (b.hom.app W x).down)))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       change _ = (R.obj.map q).hom (_ + _)
       exact (congrArg₂ (fun (a b : R.obj.obj W) ↦ a + b)
         (congrArg ULift.down (ConcreteCategory.congr_hom (a.hom.naturality q) x))
         (congrArg ULift.down (ConcreteCategory.congr_hom (b.hom.naturality q) x))).trans
         (map_add (R.obj.map q).hom _ _).symm }⟩
private theorem sectionRingPullback_add_graph {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf Y.J (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R))
    (h : ∀ W x, (t.hom.app W x).down =
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        Y.J R).obj W)
        (a.hom.app W x).down) +
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        Y.J R).obj W)
        (b.hom.app W x).down)) :
    (setPullback f).map t ≫ (sectionRingPullbackIso f R S ρ).hom =
      ringAddSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S)
        ((setPullback f).obj T)
        ((setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom)
        ((setPullback f).map b ≫ (sectionRingPullbackIso f R S ρ).hom) := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map t).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down = _
  erw [sectionRingPullbackIso_transpose]
  change _ = (@id ((InternalAbelianSheafModule.sectionRings
      X.J S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down) +
    (@id ((InternalAbelianSheafModule.sectionRings
      X.J S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map b).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down)
  erw [sectionRingPullbackIso_transpose, sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit f R S ρ W) (h W x)).trans
    (map_add (inverseImageSectionRingUnit f R S ρ W) _ _)
private noncomputable def ringNatSections {X : Site.{u}}
    (R : Sheaf X.J CommRingCat.{u + 1})
    (T : Sheaf X.J (Type (u + 1))) (n : ℕ) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ ULift.up (n : R.obj.obj W))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       exact (map_natCast (R.obj.map q).hom n).symm }⟩

private theorem sectionRingPullback_nat_graph {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf Y.J (Type (u + 1))) (n : ℕ)
    (a : T ⟶ (sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R))
    (h : ∀ W x, (a.hom.app W x).down =
      (n : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        Y.J R).obj W)) :
    (setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom =
      ringNatSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S) ((setPullback f).obj T) n := by
  let U := f.base
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) Y.J X.J
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      (n : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        X.J S).obj (U.op.obj W))
  erw [sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit f R S ρ W) (h W x)).trans
    (map_natCast (inverseImageSectionRingUnit f R S ρ W) n)

/-- The internal inverse image has the algebraic operations transported by the
inverse image of set sheaves. Source: Stacks Project, Tags 00YV and 03D2.
Proof: express both set and abelian inverse image as sheafification of the
left Kan extension along base change. The comma categories are filtered, and
the abelian forgetful functor preserves their colimits and sheafification.
Compose the resulting comparison with the inverse of rho and the equal-universe
ULift isomorphisms to obtain the ring comparison. Use the section-equivalence
counit to obtain the natural module comparison. These constructions and their
compatibility with the adjunction unit are proved by the private helpers above.
The helpers pullback_add_graph and pullback_zero_graph also prove preservation
of addition and zero before coefficient and module-equivalence transport.
The helpers pushforward_section_mul, pushforward_section_one and
pushforward_section_smul identify the pointwise algebraic operations under
pushforward. The concrete ring homomorphism inverseImageSectionRingUnit
combines the monoidal adjunction unit with the inverse coefficient map.
The lemma sectionRingPullbackIso_unit identifies it with the transpose of the
underlying ring comparison. The helpers sectionRingPullback_add_graph,
sectionRingPullback_mul_graph and sectionRingPullback_nat_graph prove the ring
operation graph equations, with zero and one as the natural-constant cases.
For each operation graph, form its two maps from the inverse image of the test
sheaf to the underlying target sheaf. Transpose through the set-sheaf adjunction.
Unit compatibility identifies the transposed maps with the source maps followed
by the abelian unit and the inverse coefficient isomorphism. The additive unit
preserves addition and zero. Its monoid-homomorphism property preserves
multiplication and one, using the pointwise tensor and unit formulas for
pushforward. The lifted module-adjunction unit preserves scalar multiplication;
compose with the linear section-equivalence counit. Thus the source graph
identity implies equality of the transposes and hence of the target maps.
Evaluating those maps gives all seven graph fields. Choose the constructed
module functor itself, with the identity comparison isomorphism.
(blueprint: lem-zl-site-inverse-image-module-flat) -/
private theorem exists_sectionModuleAlgebraicInverseImage {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    let L := Functor.sheafPullbackConstruction.sheafPullback
      f.base (Type (u + 1))
      Y.J X.J
    ∃ I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u, u + 1, u + 1} L
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R)
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          X.J S),
      Nonempty
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            Y.J R).inverse ⋙ Mod.mapModComap ρ ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            X.J S).functor ≅ I.modules) := by
  dsimp only
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    Y.J R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    X.J S
  let I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
      u + 1, u + 1} (setPullback f)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        Y.J R)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S) := by
    refine
      { ringUnderlying := sectionRingPullbackIso f R S ρ
        ringAdd := ?_
        ringMul := ?_
        ringZero := ?_
        ringOne := ?_
        modules := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
        moduleUnderlying := sectionModulePullbackIso f R S ρ
        moduleAdd := ?_
        moduleZero := ?_
        moduleSMul := ?_ }
    · intro T a b t h V x
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x)
        (sectionRingPullback_add_graph f R S ρ T a b t h))
    · intro T a b t h V x
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x)
        (sectionRingPullback_mul_graph f R S ρ T a b t h))
    · intro T a h V x
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x)
        (sectionRingPullback_nat_graph f R S ρ T 0 a h))
    · intro T a h V x
      have he := sectionRingPullback_nat_graph f R S ρ T 1 a (fun W y ↦ by
        rw [Nat.cast_one]
        exact h W y)
      simpa [ringNatSections] using
        congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x) he)
    · intro M T a b t h V x
      let QY := SheafOfModules.toSheaf ((sheafCompose Y.J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R))
      let UY := sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})
      let euY := sheafUliftIso Y.J (CategoryTheory.forget Ab.{u + 1})
      let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
      let N := eY.inverse.obj M
      have ht (q : T ⟶ (QY ⋙ sheafCompose Y.J
          (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M) :
          (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app V
            (((setPullback f).map q).hom.app V x)).down =
          (((setPullback f).map (q ≫ k) ≫
            (pullbackForgetIso f).inv.app N.X).hom.app V x) := by
        exact sectionModulePullbackIso_inv_apply f R S ρ M T _ V x
      have h' : ∀ W y, (t ≫ k).hom.app W y =
          (@id (N.X.obj.obj W) ((a ≫ k).hom.app W y)) +
          (@id (N.X.obj.obj W) ((b ≫ k).hom.app W y)) := by
        intro W y
        change ((eY.counitIso.inv.app M).val.app W).hom (t.hom.app W y).down =
          ((eY.counitIso.inv.app M).val.app W).hom (a.hom.app W y).down +
          ((eY.counitIso.inv.app M).val.app W).hom (b.hom.app W y).down
        have hh := h W y
        dsimp only [id] at hh
        exact (congrArg ((eY.counitIso.inv.app M).val.app W).hom hh).trans
          (map_add ((eY.counitIso.inv.app M).val.app W).hom _ _)
      have hp := pullback_add_graph f N.X T (a ≫ k) (b ≫ k) (t ≫ k) h'
      rw [ht t, ht a, ht b]
      exact congrArg (fun q ↦ q.hom.app V x) hp
    · intro M T a h V x
      let QY := SheafOfModules.toSheaf ((sheafCompose Y.J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          Y.J R))
      let UY := sheafCompose Y.J (CategoryTheory.forget Ab.{u + 1})
      let euY := sheafUliftIso Y.J (CategoryTheory.forget Ab.{u + 1})
      let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
      let N := eY.inverse.obj M
      have ht :
          (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app V
            (((setPullback f).map a).hom.app V x)).down =
          (((setPullback f).map (a ≫ k) ≫
            (pullbackForgetIso f).inv.app N.X).hom.app V x) := by
        exact sectionModulePullbackIso_inv_apply f R S ρ M T _ V x
      have h' : ∀ W y, (a ≫ k).hom.app W y = (0 : N.X.obj.obj W) := by
        intro W y
        change ((eY.counitIso.inv.app M).val.app W).hom (a.hom.app W y).down = 0
        have hh := h W y
        dsimp only [id] at hh
        exact (congrArg ((eY.counitIso.inv.app M).val.app W).hom hh).trans
          (map_zero ((eY.counitIso.inv.app M).val.app W).hom)
      exact ht.trans (congrArg (fun q ↦ q.hom.app V x)
        (pullback_zero_graph f N.X T (a ≫ k) h'))
    · intro M T a b t h V x
      let U := f.base
      let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
        (Type (u + 1)) Y.J X.J
      let MX := (eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor).obj M
      let RX := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        X.J S
      let sa := (setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom
      let sb := (setPullback f).map b ≫ (sectionModulePullbackIso f R S ρ).inv.app M
      let st := (setPullback f).map t ≫ (sectionModulePullbackIso f R S ρ).inv.app M
      have hp : st = moduleSMulSections RX MX ((setPullback f).obj T) sa sb := by
        apply (adj.homEquiv _ _).injective
        apply ObjectProperty.hom_ext _
        ext W y
        apply ULift.ext
        change (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app (U.op.obj W)
          (((setPullback f).map t).hom.app (U.op.obj W)
            ((adj.unit.app T).hom.app W y))).down = _
        have ht := sectionModulePullbackIso_transpose f R S ρ M T t W y
        change _ = (@id ((InternalAbelianSheafModule.sectionRings
          X.J S).obj (U.op.obj W))
          ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
            (((setPullback f).map a).hom.app (U.op.obj W)
              ((adj.unit.app T).hom.app W y))).down) •
          (@id (MX.val.obj (U.op.obj W))
          (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app (U.op.obj W)
            (((setPullback f).map b).hom.app (U.op.obj W)
              ((adj.unit.app T).hom.app W y))).down)
        have ha := sectionRingPullbackIso_transpose f R S ρ T a W y
        have hb := sectionModulePullbackIso_transpose f R S ρ M T b W y
        have hh := h W y
        dsimp only [id] at hh
        have hc := congrArg ((eY.counitIso.inv.app M).val.app W).hom hh
        have hc' := sectionModuleCounit_smul R M W
          (a.hom.app W y).down (b.hom.app W y).down
        have he := (congrArg (fun z ↦
          ((abelianAdjunction f).unit.app (eY.inverse.obj M).X).hom.app W z)
          (hc.trans hc')).trans
          (inverseImageSectionModuleUnit_smul f R S ρ (eY.inverse.obj M) W
            (a.hom.app W y).down
            (((eY.counitIso.inv.app M).val.app W).hom (b.hom.app W y).down))
        exact ht.trans (he.trans (congrArg₂
          (fun (r : (InternalAbelianSheafModule.sectionRings
            X.J S).obj (U.op.obj W))
            (m : MX.val.obj (U.op.obj W)) ↦ r • m) ha.symm hb.symm))
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x) hp)
  exact ⟨I, ⟨Iso.refl _⟩⟩

private theorem inverseImageModule_preservesFlat {X Y : Site.{u}} (f : Pullback X Y)
    (R : Sheaf Y.J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf X.J Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (abelianPullback f).obj R) [IsMonHom ρ] [IsIso ρ] :
    (Mod.mapModComap ρ).PreservesFlat := by
  have flat_of_iso (R' : Sheaf X.J CommRingCat.{u + 1})
      {M N : SheafOfModules.{u + 1}
        ((sheafCompose X.J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')}
      (e : M ≅ N) (hN : SheafOfModules.IsFlatOnSite (J := X.J) (R := R') N) :
      SheafOfModules.IsFlatOnSite (J := X.J) (R := R') M := by
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      R' M).mpr
    intro U n a s h
    let s' (i : Fin n) := e.hom.val.app (Opposite.op U) (s i)
    have hs : (∑ i, a i • s' i) = 0 := by
      change (∑ i, a i • (e.hom.val.app (Opposite.op U)) (s i)) = 0
      simpa only [map_sum, map_smul, map_zero] using
        congrArg (fun z ↦ e.hom.val.app (Opposite.op U) z) h
    obtain ⟨S, hS, hlocal⟩ :=
      (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
        R' N).mp hN U n a s' hs
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨l, b, t, ht, hb⟩ := hlocal V f hf
    refine ⟨l, b, fun j ↦ e.inv.val.app (Opposite.op V) (t j), ?_, hb⟩
    intro i
    have hi := congrArg (fun z ↦ e.inv.val.app (Opposite.op V) z) (ht i)
    simp only [map_sum, map_smul] at hi
    have hinv : e.inv.val.app (Opposite.op V)
        (e.hom.val.app (Opposite.op V) (M.val.map f.op (s i))) =
        M.val.map f.op (s i) := by
      have h := congrArg (fun z ↦ z.val.app (Opposite.op V) (M.val.map f.op (s i))) e.hom_inv_id
      exact h
    rw [← PresheafOfModules.naturality_apply] at hi
    exact hinv.symm.trans hi
  let U := f.base
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1))
    Y.J X.J
  let V := U.sheafPushforwardContinuous (Type (u + 1))
    Y.J X.J
  let adj : L ⊣ V := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U (Type (u + 1)) Y.J X.J
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    ⟨fun J _ _ ↦ ⟨inferInstance⟩⟩
  have : PreservesFiniteLimits (U.op.lan :
      (Y.Cᵒᵖ ⥤ Type (u + 1)) ⥤ X.Cᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.preservesFiniteLimits_op_lan_of_flat U
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  obtain ⟨I, ⟨ei⟩⟩ := exists_sectionModuleAlgebraicInverseImage f R S ρ
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    Y.J R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    X.J S
  refine ⟨fun {M} hM ↦ ?_⟩
  have hsec := (InternalAbelianSheafModule.flat_iff_sectionModule
    Y.J R M).mp hM
  have hi := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
    u + 1, u + 1}
    L V adj I (eY.functor.obj M) hsec
  let e : eX.functor.obj ((Mod.mapModComap ρ).obj M) ≅
      I.modules.obj (eY.functor.obj M) :=
    (Mod.mapModComap ρ ⋙ eX.functor).mapIso (eY.unitIso.app M) ≪≫
      ei.app (eY.functor.obj M)
  have ht := flat_of_iso
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      X.J S) e hi
  exact (InternalAbelianSheafModule.flat_iff_sectionModule
    X.J S _).mpr ht

end CategoryTheory.SiteInverseImageModuleFlat
end

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace CategoryTheory.SiteInverseImageModuleFlat
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

end CategoryTheory.SiteInverseImageModuleFlat
