/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Algebraic presentation of pro-étale internal inverse image
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

/- The concrete inverse image and its comparison after forgetting abelian groups. -/
private noncomputable def setPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
private noncomputable def pullbackForgetIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*[Ab.{u + 1}] ⋙ sheafCompose (Scheme.ProEt.topology X)
        (CategoryTheory.forget Ab.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1}) ⋙
        setPullback f := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let G := CategoryTheory.forget Ab.{u + 1}
  have (P : Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) :
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
  let eSh := sheafComposeNatIso (Scheme.ProEt.topology X) G
    (sheafificationAdjunction _ Ab.{u + 1})
    (sheafificationAdjunction _ (Type (u + 1)))
  exact Functor.isoWhiskerLeft
      (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1} ⋙ U.op.lan) eSh.symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (Functor.isoWhiskerRight eLan
        (presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1))))


/- Concrete coefficient and module comparisons, including the universe lifts. -/
private noncomputable def sheafUliftIso
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A : Type*} [Category A] (G : A ⥤ Type (u + 1))
    [J.HasSheafCompose G] [J.HasSheafCompose (G ⋙ uliftFunctor.{u + 1, u + 1})] :
    sheafCompose J (G ⋙ uliftFunctor.{u + 1, u + 1}) ≅ sheafCompose J G :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun W ↦ uliftTrivial (G.obj (M.obj.obj W)))
      (by intros; rfl))) (by intros; rfl)

private noncomputable def sectionRingUnderlyingIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (sheafCompose (Scheme.ProEt.topology X)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R) ≅
    (sheafCompose (Scheme.ProEt.topology X) (CategoryTheory.forget Ab.{u + 1})).obj R :=
  (sheafUliftIso (Scheme.ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).app _

private noncomputable def sectionRingPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    let L := setPullback f
    L.obj ((sheafCompose (Scheme.ProEt.topology Y)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R)) ≅
    (sheafCompose (Scheme.ProEt.topology X)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S) :=
  (setPullback f).mapIso (sectionRingUnderlyingIso R) ≪≫
    ((pullbackForgetIso f).app R).symm ≪≫
    (sheafCompose (Scheme.ProEt.topology X)
      (CategoryTheory.forget Ab.{u + 1})).mapIso (asIso ρ).symm ≪≫
    (sectionRingUnderlyingIso S).symm



private noncomputable def sectionModulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) R
    let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) S
    (eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor) ⋙ SheafOfModules.toSheaf _ ⋙
      sheafCompose (Scheme.ProEt.topology X)
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1}) ≅
    (SheafOfModules.toSheaf _ ⋙ sheafCompose (Scheme.ProEt.topology Y)
      (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})) ⋙ setPullback f := by
  dsimp only
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) S
  let I := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
  let UX := sheafCompose (Scheme.ProEt.topology X) (CategoryTheory.forget Ab.{u + 1})
  let UY := sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
  let RY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R)
  let F := SheafOfModules.toSheaf RY ⋙ UY
  let euX := sheafUliftIso (Scheme.ProEt.topology X) (CategoryTheory.forget Ab.{u + 1})
  let euY := sheafUliftIso (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
  let e₁ : I ⋙ SheafOfModules.toSheaf _ ⋙ UX ≅
      eY.inverse ⋙ Mod.forget R ⋙ UY ⋙ setPullback f :=
    Functor.isoWhiskerLeft (eY.inverse ⋙ Mod.forget R) (pullbackForgetIso f)
  let e₂ : eY.inverse ⋙ Mod.forget R ⋙ UY ≅ F :=
    Functor.isoWhiskerRight eY.counitIso F
  exact Functor.isoWhiskerLeft (I ⋙ SheafOfModules.toSheaf _) euX ≪≫
    e₁ ≪≫ Functor.isoWhiskerRight e₂ (setPullback f) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.toSheaf _) euY.symm) (setPullback f)


private theorem sectionModulePullbackIso_inv_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) R
    let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) S
    let I := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
    let QY := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R))
    let QX := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S))
    let UY := sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
    let euY := sheafUliftIso (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
    let euX := sheafUliftIso (Scheme.ProEt.topology X) (CategoryTheory.forget Ab.{u + 1})
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

private theorem sectionModulePullbackIso_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) R
    let QY := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R))
    let UY := sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
    let euY := sheafUliftIso (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R)))
      (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
      (q : T ⟶ (QY ⋙ sheafCompose (Scheme.ProEt.topology Y)
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M)
      (V : X.ProEtᵒᵖ) (x : ((setPullback f).obj T).obj.obj V),
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
private theorem setPullback_unit_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) :
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app G).hom =
      U.op.leftKanExtensionUnit G.obj ≫ Functor.whiskerLeft U.op
        (toSheafify (Scheme.ProEt.topology X) (U.op.leftKanExtension G.obj)) := by
  dsimp only
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction (Type (u + 1))).comp
      (sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1))))
    (fullyFaithfulSheafToPresheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
    (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback U
      (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
    (R := U.sheafPushforwardContinuous (Type (u + 1))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h
private theorem abelianPullback_unit_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app G).hom =
      U.op.leftKanExtensionUnit G.obj ≫ Functor.whiskerLeft U.op
        (toSheafify (Scheme.ProEt.topology X) (U.op.leftKanExtension G.obj)) := by
  dsimp only
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction Ab.{u + 1}).comp
      (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}))
    (fullyFaithfulSheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback U
      Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
    (R := U.sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h

private theorem pullbackForgetIso_unit_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app
        ((sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})).obj R)).hom ≫
      Functor.whiskerLeft U.op ((pullbackForgetIso f).inv.app R).hom =
    Functor.whiskerRight ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app R).hom
      (CategoryTheory.forget Ab.{u + 1}) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let G := CategoryTheory.forget Ab.{u + 1}
  have (P : Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) :
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
private noncomputable def sumSections {X : Scheme.{u}}
    {T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))}
    (A : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
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

private theorem pullback_add_graph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A)
    (h : ∀ W x, t.hom.app W x = (@id (A.obj.obj W) (a.hom.app W x)) +
      (@id (A.obj.obj W) (b.hom.app W x))) :
    (setPullback f).map t ≫ (pullbackForgetIso f).inv.app A =
      sumSections ((f)^*[Ab.{u + 1}].obj A)
        ((setPullback f).map a ≫ (pullbackForgetIso f).inv.app A)
        ((setPullback f).map b ≫ (pullbackForgetIso f).inv.app A) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  change t ≫ adj.homEquiv _ _ ((pullbackForgetIso f).inv.app A) = _
  have he : (adj.homEquiv _ _ ((pullbackForgetIso f).inv.app A)).hom =
      Functor.whiskerRight ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := pullbackForgetIso_unit_hom f A
  have hq (q : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A) :
      (adj.homEquiv _ _ ((setPullback f).map q ≫
        (pullbackForgetIso f).inv.app A)).hom =
      q.hom ≫ Functor.whiskerRight
        ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := by
    erw [adj.homEquiv_naturality_left]
    exact congrArg (fun z ↦ q.hom ≫ z) he
  apply ObjectProperty.hom_ext _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  ext W x
  have ha := ConcreteCategory.congr_hom (NatTrans.congr_app (hq a) W) x
  have hb := ConcreteCategory.congr_hom (NatTrans.congr_app (hq b) W) x
  change ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A).hom.app W
      (t.hom.app W x) = _
  rw [h W x, map_add]
  change _ = (@id (((f)^*[Ab.{u + 1}].obj A).obj.obj (U.op.obj W))
    (((pullbackForgetIso f).inv.app A).hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W) ((adj.unit.app T).hom.app W x)))) +
    (@id (((f)^*[Ab.{u + 1}].obj A).obj.obj (U.op.obj W))
    (((pullbackForgetIso f).inv.app A).hom.app (U.op.obj W)
      (((setPullback f).map b).hom.app (U.op.obj W) ((adj.unit.app T).hom.app W x))))
  exact congrArg₂ (fun (a b : ((f)^*[Ab.{u + 1}].obj A).obj.obj (U.op.obj W)) ↦ a + b)
    ha.symm hb.symm
private noncomputable def zeroSections {X : Scheme.{u}}
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (A : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (0 : A.obj.obj W))
     naturality := fun V W q ↦ by
       ext x
       exact (map_zero (A.obj.map q).hom).symm }⟩

private theorem pullback_zero_graph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
    (a : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A)
    (h : ∀ W x, a.hom.app W x = (0 : A.obj.obj W)) :
    (setPullback f).map a ≫ (pullbackForgetIso f).inv.app A =
      zeroSections ((setPullback f).obj T) ((f)^*[Ab.{u + 1}].obj A) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  change a ≫ adj.homEquiv _ _ ((pullbackForgetIso f).inv.app A) = _
  have he : (adj.homEquiv _ _ ((pullbackForgetIso f).inv.app A)).hom =
      Functor.whiskerRight ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := pullbackForgetIso_unit_hom f A
  apply ObjectProperty.hom_ext _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  ext W x
  change ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A).hom.app W
      (a.hom.app W x) = (0 : ((f)^*[Ab.{u + 1}].obj A).obj.obj (U.op.obj W))
  rw [h W x, map_zero]

/- Pointwise ring and action formulas for pushforward and its adjunction unit. -/
private theorem section_mul {X : Scheme.{u}}
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : X.ProEtᵒᵖ) (a b : S.obj.obj W) :
    let RX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj W
    @HMul.hMul RX RX RX inferInstance a b =
      (μ[S]).hom.app W ((Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S S).app W
          (a ⊗ₜ[ℤ] b)) := rfl

private theorem section_one {X : Scheme.{u}}
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : X.ProEtᵒᵖ) :
    let RX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj W
    (1 : RX) = (η[S]).hom.app W ((Functor.LaxMonoidal.ε
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})).app W (ULift.up 1)) := rfl

private theorem pushforward_section_mul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Y.ProEtᵒᵖ)
    (a b : S.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W)) :
    let RY := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y)
      ((f)_*[Ab.{u + 1}].obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W)
    @HMul.hMul RY RY RY inferInstance a b =
      @HMul.hMul RX RX RX inferInstance a b := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    U Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) S S W
  refine (section_mul ((f)_*[Ab.{u + 1}].obj S) W a b).trans
    ((Eq.trans ?_ (section_mul S (U.op.obj W) a b).symm))
  have hmul : μ[((f)_*[Ab.{u + 1}].obj S)] =
      Functor.LaxMonoidal.μ ((f)_*[Ab.{u + 1}]) S S ≫
        ((f)_*[Ab.{u + 1}]).map μ[S] := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).map hmul) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
  have ht' := congrArg (fun x : (S ⊗ S).obj.obj (U.op.obj W) ↦
    (μ[S]).hom.app (U.op.obj W) x) ht
  exact ht'

private theorem pushforward_section_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Y.ProEtᵒᵖ) :
    let RY := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y)
      ((f)_*[Ab.{u + 1}].obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W)
    @OfNat.ofNat RY 1 inferInstance = @OfNat.ofNat RX 1 inferInstance := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    U Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) W
  refine (section_one ((f)_*[Ab.{u + 1}].obj S) W).trans
    ((Eq.trans ?_ (section_one S (U.op.obj W)).symm))
  have hunit : η[((f)_*[Ab.{u + 1}].obj S)] =
      Functor.LaxMonoidal.ε ((f)_*[Ab.{u + 1}]) ≫
        ((f)_*[Ab.{u + 1}]).map η[S] := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).map hunit) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (ULift.up 1)
  have ht' := congrArg (fun x : (𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).obj.obj
      (U.op.obj W) ↦ (η[S]).hom.app (U.op.obj W) x) ht
  exact ht'
private theorem section_smul {X : Scheme.{u}}
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (W : X.ProEtᵒᵖ) (a : S.obj.obj W) (b : M.X.obj.obj W) :
    let RX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) S).obj M).val.obj W
    @HSMul.hSMul RX MX MX inferInstance a b =
      (Mod.act M.X).hom.app W ((Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S M.X).app W
          (a ⊗ₜ[ℤ] b)) := rfl

private theorem pushforward_section_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (W : Y.ProEtᵒᵖ)
    (a : S.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W))
    (b : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W)) :
    let RY := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y)
      ((f)_*[Ab.{u + 1}].obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W)
    let MY := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology Y) ((f)_*[Ab.{u + 1}].obj S)).obj
        ((((f)_*[Ab.{u + 1}]).mapMod S).obj M)).val.obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) S).obj M).val.obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W)
    @HSMul.hSMul RY MY MY inferInstance a b =
      @HSMul.hSMul RX MX MX inferInstance a b := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    U Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) S M.X W
  refine (section_smul _ ((((f)_*[Ab.{u + 1}]).mapMod S).obj M) W a b).trans
    ((Eq.trans ?_ (section_smul S M (U.op.obj W) a b).symm))
  have hact : Mod.act (((((f)_*[Ab.{u + 1}]).mapMod S).obj M).X) =
      Functor.LaxMonoidal.μ ((f)_*[Ab.{u + 1}]) S M.X ≫
        ((f)_*[Ab.{u + 1}]).map (Mod.act M.X) := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).map hact) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
  have ht' := congrArg (fun x : (S ⊗ M.X).obj.obj (U.op.obj W) ↦
    (Mod.act M.X).hom.app (U.op.obj W) x) ht
  exact ht'
private theorem section_comap_smul {X : Scheme.{u}}
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (W : X.ProEtᵒᵖ) (a : R.obj.obj W) (b : M.X.obj.obj W) :
    let RR := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) R).obj W
    let RS := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj W
    let MR := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) R).obj ((Mod.comap φ).obj M)).val.obj W
    let MS := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) S).obj M).val.obj W
    @HSMul.hSMul RR MR MR inferInstance a b =
      @HSMul.hSMul RS MS MS inferInstance (φ.hom.app W a) b := by
  let H := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
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

private noncomputable def sectionRingMap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (g : R ⟶ S) [IsMonHom g] (W : X.ProEtᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) R).obj W →+*
      (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj W := by
  let H := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapCommMon ⋙
    (Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor
  exact InternalAbelianSheafModule.ringHom
    ((H.map (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) ⟨g⟩)).app W).hom.hom

private noncomputable def pushforwardSectionRingHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Y.ProEtᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y)
      ((f)_*[Ab.{u + 1}].obj S)).obj W →+*
    (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W) where
  toFun := fun a ↦ a
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := pushforward_section_one f S W
  map_mul' a b := pushforward_section_mul f S W a b

private noncomputable def inverseImageSectionRingUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (W : Y.ProEtᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y) R).obj W →+*
    (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj W) :=
by
  haveI : IsMonHom ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app R) :=
    (upperStarLowerStarAdjunction Ab.{u + 1} f).isMonHom_unitAlgHom R
  haveI : IsMonHom (asIso ρ).inv := inferInstance
  haveI : IsMonHom (((f)_*[Ab.{u + 1}]).map (asIso ρ).inv) :=
    Functor.map.instIsMonHom (F := (f)_*[Ab.{u + 1}]) _ _ (asIso ρ).inv
  exact (pushforwardSectionRingHom f S W).comp
    (sectionRingMap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app R ≫
      ((f)_*[Ab.{u + 1}]).map (asIso ρ).inv) W)

private theorem sectionModuleCounit_smul {Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) R
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R)))
      (W : Y.ProEtᵒᵖ)
      (a : (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y) R).obj W)
      (b : M.val.obj W),
    let RR := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y) R).obj W
    let NM := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology Y) R).obj (eY.inverse.obj M)).val.obj W
    ((eY.counitIso.inv.app M).val.app W).hom (a • b) =
      @HSMul.hSMul RR NM NM inferInstance a
        (((eY.counitIso.inv.app M).val.app W).hom b) := by
  intro eY M W a b
  exact ((eY.counitIso.inv.app M).val.app W).hom.map_smul a b

private theorem inverseImageSectionModuleUnit_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    (W : Y.ProEtᵒᵖ) (a : R.obj.obj W) (b : N.X.obj.obj W) :
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    let RY := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y) R).obj W
    let SX := (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology X) S).obj
      (U.op.obj W)
    let MY := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology Y) R).obj N).val.obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) S).obj ((Mod.mapModComap ρ).obj N)).val.obj (U.op.obj W)
    ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app N.X).hom.app W
      (@HSMul.hSMul RY MY MY inferInstance a b) =
      @HSMul.hSMul SX MX MX inferInstance (inverseImageSectionRingUnit f R S ρ W a)
        (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app N.X).hom.app W b) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  let P := (((f)^*[Ab.{u + 1}]).mapMod R).obj N
  let Z := (((f)_*[Ab.{u + 1}]).mapMod ((f)^*[Ab.{u + 1}].obj R)).obj P
  let j := (adj.mapModAdjunction R).unit.app N
  let H := InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology Y) R
  have hj := (((H.map j).val.app W).hom).map_smul
    (show (InternalAbelianSheafModule.sectionRings (Scheme.ProEt.topology Y) R).obj W from a)
    (show (H.obj N).val.obj W from b)
  have hc := section_comap_smul R ((f)_*[Ab.{u + 1}].obj
      ((f)^*[Ab.{u + 1}].obj R)) (adj.unitAlgHom R) Z W a
      (j.hom.hom.app W b)
  have hp := pushforward_section_smul f ((f)^*[Ab.{u + 1}].obj R) P W
    ((adj.unit.app R).hom.app W a) (j.hom.hom.app W b)
  have hd := section_comap_smul S ((f)^*[Ab.{u + 1}].obj R) ρ P (U.op.obj W)
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

private theorem sectionRingPullbackIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (W : Y.ProEtᵒᵖ) (r : ULift.{u + 1} (R.obj.obj W)) :
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      ((adj.unit.app ((sheafCompose (Scheme.ProEt.topology Y)
        (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology Y) R))).hom.app W r)).down =
        inverseImageSectionRingUnit f R S ρ W r.down := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf (Scheme.ProEt.topology Y)
      (Type (u + 1))).map (adj.unit.naturality (sectionRingUnderlyingIso R).hom)) W) r
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackForgetIso_unit_hom f R) W) r.down
  have hn' := congrArg (fun x ↦ ((pullbackForgetIso f).inv.app R).hom.app
    (U.op.obj W) x) hn
  exact congrArg (fun x ↦ ((asIso ρ).inv.hom.app (U.op.obj W)) x) (hn'.symm.trans hu)

/- Ring operation graphs, proved by transposition through the set adjunction. -/
private noncomputable def ringMulSections {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
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
private noncomputable def moduleSMulSections {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
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

private theorem sectionModulePullbackIso_transpose {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) R
    let QY := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R))
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R)))
      (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
      (q : T ⟶ (QY ⋙ sheafCompose (Scheme.ProEt.topology Y)
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M)
      (W : Y.ProEtᵒᵖ) (x : T.obj.obj W),
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (((sectionModulePullbackIso f R S ρ).inv.app M).hom.app (U.op.obj W)
      (((setPullback f).map q).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app (eY.inverse.obj M).X).hom.app W
        (((eY.counitIso.inv.app M).val.app W).hom (q.hom.app W x).down) := by
  intro eY QY M T q W x U adj
  let UY := sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
  let euY := sheafUliftIso (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
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
    (NatTrans.congr_app (congrArg (sheafToPresheaf (Scheme.ProEt.topology Y)
      (Type (u + 1))).map (adj.unit.naturality (q ≫ k))) W) x
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackForgetIso_unit_hom f N.X) W) ((q ≫ k).hom.app W x)
  have hn' := congrArg (fun z ↦ ((pullbackForgetIso f).inv.app N.X).hom.app
    (U.op.obj W) z) hn
  exact ht.trans (hn'.symm.trans hu)

private theorem sectionRingPullbackIso_transpose {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
    (q : T ⟶ (sheafCompose (Scheme.ProEt.topology Y)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R)) (W : Y.ProEtᵒᵖ) (x : T.obj.obj W) :
    let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
      (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map q).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      inverseImageSectionRingUnit f R S ρ W (q.hom.app W x).down := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf (Scheme.ProEt.topology Y)
      (Type (u + 1))).map (adj.unit.naturality q)) W) x
  have hn' := congrArg (fun z ↦
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W) z).down) hn
  exact hn'.symm.trans (sectionRingPullbackIso_unit f R S ρ W (q.hom.app W x))
private theorem sectionRingPullback_mul_graph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose (Scheme.ProEt.topology Y)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R))
    (h : ∀ W x, (t.hom.app W x).down =
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj W)
        (a.hom.app W x).down) *
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj W)
        (b.hom.app W x).down)) :
    (setPullback f).map t ≫ (sectionRingPullbackIso f R S ρ).hom =
      ringMulSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S)
        ((setPullback f).obj T)
        ((setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom)
        ((setPullback f).map b ≫ (sectionRingPullbackIso f R S ρ).hom) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map t).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down = _
  erw [sectionRingPullbackIso_transpose]
  change _ = (@id ((InternalAbelianSheafModule.sectionRings
      (Scheme.ProEt.topology X) S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down) *
    (@id ((InternalAbelianSheafModule.sectionRings
      (Scheme.ProEt.topology X) S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map b).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down)
  erw [sectionRingPullbackIso_transpose, sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit f R S ρ W) (h W x)).trans
    (map_mul (inverseImageSectionRingUnit f R S ρ W) _ _)
private noncomputable def ringAddSections {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
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
private theorem sectionRingPullback_add_graph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose (Scheme.ProEt.topology Y)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R))
    (h : ∀ W x, (t.hom.app W x).down =
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj W)
        (a.hom.app W x).down) +
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj W)
        (b.hom.app W x).down)) :
    (setPullback f).map t ≫ (sectionRingPullbackIso f R S ρ).hom =
      ringAddSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S)
        ((setPullback f).obj T)
        ((setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom)
        ((setPullback f).map b ≫ (sectionRingPullbackIso f R S ρ).hom) := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map t).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down = _
  erw [sectionRingPullbackIso_transpose]
  change _ = (@id ((InternalAbelianSheafModule.sectionRings
      (Scheme.ProEt.topology X) S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down) +
    (@id ((InternalAbelianSheafModule.sectionRings
      (Scheme.ProEt.topology X) S).obj (U.op.obj W))
    ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map b).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down)
  erw [sectionRingPullbackIso_transpose, sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit f R S ρ W) (h W x)).trans
    (map_add (inverseImageSectionRingUnit f R S ρ W) _ _)
private noncomputable def ringNatSections {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (n : ℕ) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ ULift.up (n : R.obj.obj W))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       exact (map_natCast (R.obj.map q).hom n).symm }⟩

private theorem sectionRingPullback_nat_graph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) (n : ℕ)
    (a : T ⟶ (sheafCompose (Scheme.ProEt.topology Y)
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R))
    (h : ∀ W x, (a.hom.app W x).down =
      (n : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj W)) :
    (setPullback f).map a ≫ (sectionRingPullbackIso f R S ρ).hom =
      ringNatSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S) ((setPullback f).obj T) n := by
  let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso f R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback f).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      (n : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S).obj (U.op.obj W))
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
(auxiliary; not a blueprint node) -/
theorem exists_sectionModuleAlgebraicInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (f)^*[Ab.{u + 1}].obj R) [IsMonHom ρ] [IsIso ρ] :
    let L := Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    ∃ I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u, u + 1, u + 1} L
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R)
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) S),
      Nonempty
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            (Scheme.ProEt.topology Y) R).inverse ⋙ Mod.mapModComap ρ ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) S).functor ≅ I.modules) := by
  dsimp only
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) S
  let I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
      u + 1, u + 1} (setPullback f)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S) := by
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
      let QY := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R))
      let UY := sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
      let euY := sheafUliftIso (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
      let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
      let N := eY.inverse.obj M
      have ht (q : T ⟶ (QY ⋙ sheafCompose (Scheme.ProEt.topology Y)
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
      let QY := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R))
      let UY := sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
      let euY := sheafUliftIso (Scheme.ProEt.topology Y) (CategoryTheory.forget Ab.{u + 1})
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
      let U := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
      let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
        (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      let MX := (eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor).obj M
      let RX := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S
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
          (Scheme.ProEt.topology X) S).obj (U.op.obj W))
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
          ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app (eY.inverse.obj M).X).hom.app W z)
          (hc.trans hc')).trans
          (inverseImageSectionModuleUnit_smul f R S ρ (eY.inverse.obj M) W
            (a.hom.app W y).down
            (((eY.counitIso.inv.app M).val.app W).hom (b.hom.app W y).down))
        exact ht.trans (he.trans (congrArg₂
          (fun (r : (InternalAbelianSheafModule.sectionRings
            (Scheme.ProEt.topology X) S).obj (U.op.obj W))
            (m : MX.val.obj (U.op.obj W)) ↦ r • m) ha.symm hb.symm))
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x) hp)
  exact ⟨I, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale
