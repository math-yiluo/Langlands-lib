/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Finite-basis tensor evaluation

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CY, 03DA and 03DB;
finite-basis consequence with explicit section formulas.
(blueprint: lem-pur-based-sheaf-tensor-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.Limits.limit

universe u vC uC
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}}

/-- Evaluate a finite power using its coordinate projections.
Source: Stacks 03DB, sectionwise limits
(blueprint: lem-pur-based-sheaf-tensor-evaluation). -/
def basedTensorProductSections (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ M).val.obj U ≅
      ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) :=
  PreservesProduct.iso
    (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
      (fun _ : Fin d ↦ M) ≪≫ ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem sections_coordinate (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) (x : (∏ᶜ fun _ : Fin d ↦ M).val.obj U) (i : Fin d) :
    (basedTensorProductSections d M U).hom x i = (Pi.π (fun _ : Fin d ↦ M) i).val.app U x := by
  let E := evaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U
  let f := fun _ : Fin d ↦ M
  let q : ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) ⟶ M.val.obj U :=
    ModuleCat.ofHom (LinearMap.proj i)
  have h : (basedTensorProductSections d M U).hom ≫ q = (Pi.π f i).val.app U := by
    unfold basedTensorProductSections
    exact (Category.assoc (PreservesProduct.iso E f).hom
      (ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)).hom q).trans
      ((congrArg (fun g ↦ (PreservesProduct.iso E f).hom ≫ g)
        (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : Fin d ↦ M.val.obj U) i)).trans
        (piComparison_comp_π E f i))
  exact congrArg (fun g ↦ g x) h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem sectionProduct_ext (d : ℕ)
    (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x y : (∏ᶜ fun _ : Fin d ↦ M).val.obj V)
    (h : ∀ i : Fin d, (Pi.π (fun _ : Fin d ↦ M) i).val.app V x =
      (Pi.π (fun _ : Fin d ↦ M) i).val.app V y) : x = y := by
  apply (basedTensorProductSections (R := R) d M V).toLinearEquiv.injective
  funext i
  exact (sections_coordinate (R := R) d M V x i).trans
    ((h i).trans (sections_coordinate (R := R) d M V y i).symm)

noncomputable local instance
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {V W : Cᵒᵖ} (f : V ⟶ W) :
    Module (R.obj.obj W)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
          (M.val.obj W)) :=
  inferInstanceAs (Module (R.obj.obj W) (M.val.obj W))

private theorem changeMap_tmul (φ : R ⟶ S)
    (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {V W : Cᵒᵖ} (f : V ⟶ W) (s : S.obj.obj V) (m : M.val.obj V) :
    changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) =
      S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m :=
  Classical.choose_spec (exists_changeOfRingsMap φ M f) s m

attribute [local irreducible] basedTensorProductSections changeOfRingsMap

@[irreducible] private def coordinateEquiv {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {d : ℕ}
    (q : (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B) ≃ₗ[A] (Fin d → A))
    (M : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M) ≃ₗ[A]
      (Fin d → M) := by
  letI : Module A B := Module.compHom B φ
  exact TensorProduct.comm A B M ≪≫ₗ q.lTensor M ≪≫ₗ
    TensorProduct.piScalarRight A A M (Fin d)

private theorem coordinateEquiv_tmul {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {d : ℕ}
    (q : (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B) ≃ₗ[A] (Fin d → A))
    (M : ModuleCat.{u} A) (a : B) (x : M) (i : Fin d) :
    coordinateEquiv φ q M (a ⊗ₜ[A, φ] x) i = q a i • x := by
  let : Module A B := Module.compHom B φ
  unfold coordinateEquiv
  change (TensorProduct.piScalarRight A A M (Fin d))
    (q.lTensor M ((TensorProduct.comm A B M) (a ⊗ₜ[A] x))) i = _
  change (TensorProduct.piScalarRightHom A A M (Fin d)) (x ⊗ₜ[A] q a) i = _
  exact congrArg (fun z ↦ z i) (TensorProduct.piScalarRightHom_tmul A A M (Fin d) x (q a))

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

@[irreducible] private def basisCoordinates (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S))) (U : Cᵒᵖ) :
    (ModuleCat.restrictScalars (φ.hom.app U).hom).obj
      (ModuleCat.of (S.obj.obj U) (S.obj.obj U)) ≃ₗ[R.obj.obj U] (Fin d → R.obj.obj U) :=
  ((evaluation (𝓡 R) U).mapIso e.symm ≪≫
    basedTensorProductSections d (unit (𝓡 R)) U).toLinearEquiv

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem basisCoordinates_apply (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (U : Cᵒᵖ) (a : S.obj.obj U) (i : Fin d) :
    basisCoordinates φ d e U a i =
      (e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app U a := by
  unfold basisCoordinates
  exact sections_coordinate d (unit (𝓡 R)) U (e.inv.val.app U a) i

@[irreducible] private def tensorCoordinateApp (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{vC, uC, u} φ M)).obj V ≅ (∏ᶜ fun _ : Fin d ↦ M).val.obj V :=
  (coordinateEquiv (φ.hom.app V).hom (basisCoordinates φ d e V)
    (M.val.obj V)).toModuleIso ≪≫ (basedTensorProductSections (R := R) d M V).symm

noncomputable local instance (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) :
    SMul ((unit (𝓡 R)).val.obj V) (M.val.obj V) :=
  inferInstanceAs (SMul (R.obj.obj V) (M.val.obj V))

private theorem tensorCoordinateApp_tmul (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ)
    (s : S.obj.obj V) (m : M.val.obj V) (i : Fin d) :
    (Pi.π (fun _ : Fin d ↦ M) i).val.app V
      ((tensorCoordinateApp φ d e M V).hom (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) =
      ((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V s) • m := by
  have hp := sections_coordinate (R := R) d M V
    ((tensorCoordinateApp φ d e M V).hom
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) i
  refine hp.symm.trans ?_
  unfold tensorCoordinateApp
  change (basedTensorProductSections (R := R) d M V).hom
    ((basedTensorProductSections (R := R) d M V).inv
      (coordinateEquiv (φ.hom.app V).hom (basisCoordinates φ d e V)
        (M.val.obj V) (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) i = _
  exact (congrArg (fun z ↦ z i)
    ((basedTensorProductSections (R := R) d M V).inv_hom_id_apply _)).trans
    ((coordinateEquiv_tmul (φ.hom.app V).hom (basisCoordinates φ d e V)
      (M.val.obj V) s m i).trans
        (congrArg (fun r ↦ r • m) (basisCoordinates_apply φ d e V s i)))

@[irreducible] private def tensorCoordinates (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf.{vC, uC, u} φ M) ≅
      (∏ᶜ fun _ : Fin d ↦ M).val :=
  PresheafOfModules.isoMk (tensorCoordinateApp φ d e M) (by
    intro V W f
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (map_add _ x y).symm)
    | tmul s m =>
      apply sectionProduct_ext d M W
      intro i
      change (Pi.π (fun _ : Fin d ↦ M) i).val.app W
          ((tensorCoordinateApp φ d e M W).hom (changeOfRingsMap φ M f
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) =
        (Pi.π (fun _ : Fin d ↦ M) i).val.app W
          ((∏ᶜ fun _ : Fin d ↦ M).val.map f
            ((tensorCoordinateApp φ d e M V).hom
              (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)))
      have ht := congrArg ((Pi.π (fun _ : Fin d ↦ M) i).val.app W ∘
        (tensorCoordinateApp φ d e M W).hom) (changeMap_tmul φ M f s m)
      exact ht.trans ((tensorCoordinateApp_tmul φ d e M W _ _ i).trans (by
        have hπ := PresheafOfModules.naturality_apply
          (Pi.π (fun _ : Fin d ↦ M) i).val f
          ((tensorCoordinateApp φ d e M V).hom
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))
        have hc := tensorCoordinateApp_tmul φ d e M V s m i
        have hl := PresheafOfModules.map_smul M.val f
          (((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V) s) m
        have hb := PresheafOfModules.naturality_apply
          (e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val f s
        exact (congrArg (fun r : R.obj.obj W ↦
          r • (show M.val.obj W from M.val.map f m)) hb).trans
          (hl.symm.trans ((congrArg (M.val.map f) hc).symm.trans hπ.symm)))))

private theorem tensor_isSheaf (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) :
    Presheaf.IsSheaf J (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf := by
  change Presheaf.IsSheaf J
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{vC, uC, u} φ F)).presheaf
  exact (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf (𝓡 R).obj).mapIso (tensorCoordinates φ d e F))).2
      (∏ᶜ fun _ : Fin d ↦ F).isSheaf

private def tensorPresheafFunctor (φ : R ⟶ S) :
    SheafOfModules.{u} (𝓡 R) ⥤ PresheafOfModules.{u} (𝓡 S).obj where
  obj F := changeOfRingsPresheaf.{vC, uC, u} φ F
  map {F G} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality φ F f }
  map_id F := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id _
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_comp _ _

private def tensorFunctor (φ : R ⟶ S) :
    SheafOfModules.{u} (𝓡 R) ⥤ SheafOfModules.{u} (𝓡 S) :=
  tensorPresheafFunctor φ ⋙ PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)

private def tensorUnit (φ : R ⟶ S) (F : SheafOfModules.{u} (𝓡 R)) :
    changeOfRingsPresheaf.{vC, uC, u} φ F ⟶ (changeOfRings.{vC, uC, u} φ F).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
    (changeOfRingsPresheaf.{vC, uC, u} φ F)

private theorem tensorUnit_isIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) : IsIso (tensorUnit φ F) := by
  have := isIso_toSheafify J (tensor_isSheaf φ d e F)
  have : IsIso ((PresheafOfModules.toPresheaf (𝓡 S).obj).map (tensorUnit φ F)) :=
    inferInstanceAs (IsIso (toSheafify J (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf))
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf (𝓡 S).obj)

private theorem tensorUnit_naturality (φ : R ⟶ S)
    {F G : SheafOfModules.{u} (𝓡 R)} (f : F ⟶ G) :
    (tensorPresheafFunctor φ).map f ≫ tensorUnit φ G =
      tensorUnit φ F ≫ ((tensorFunctor φ).map f).val := by
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.naturality
    ((tensorPresheafFunctor φ).map f)

private theorem tensorCoordinates_naturality (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    {F G : SheafOfModules.{u} (𝓡 R)} (f : F ⟶ G) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((tensorPresheafFunctor φ).map f) ≫ (tensorCoordinates φ d e G).hom =
      (tensorCoordinates φ d e F).hom ≫ (Limits.Pi.map (fun _ : Fin d ↦ f)).val := by
  ext V x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)
  | tmul s m =>
    apply sectionProduct_ext d G V
    intro i
    change (Pi.π (fun _ : Fin d ↦ G) i).val.app V
      ((tensorCoordinates φ d e G).hom.app V
        (((tensorPresheafFunctor φ).map f).app V (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) = _
    have ht : ((tensorPresheafFunctor φ).map f).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) =
        s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] f.val.app V m := by
      exact ModuleCat.ExtendScalars.map_tmul _ _ _ _
    have hp := congrArg (fun g ↦ g.val.app V
      ((tensorCoordinateApp φ d e F V).hom (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)))
      (Pi.map_π (fun _ : Fin d ↦ f) i)
    have hN := tensorCoordinateApp_tmul φ d e G V s (f.val.app V m) i
    have hM := tensorCoordinateApp_tmul φ d e F V s m i
    have hT := congrArg ((Pi.π (fun _ : Fin d ↦ G) i).val.app V ∘
      (tensorCoordinateApp φ d e G V).hom) ht
    unfold tensorCoordinates
    exact hT.trans (hN.trans (((f.val.app V).hom.map_smul _ _).symm.trans
      ((congrArg (f.val.app V) hM).symm.trans hp.symm)))

@[irreducible] private def tensorSheafCoordinates (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) :
    (restrictScalars.{u} (𝓻 φ)).obj ((tensorFunctor φ).obj F) ≅
      ∏ᶜ fun _ : Fin d ↦ F := by
  have := tensorUnit_isIso φ d e F
  let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
  let η := Q.mapIso (asIso (tensorUnit φ F))
  let β := tensorCoordinates φ d e F
  exact
    { hom := ⟨η.inv ≫ β.hom⟩
      inv := ⟨β.inv ≫ η.hom⟩
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        change (η.inv ≫ β.hom) ≫ (β.inv ≫ η.hom) = 𝟙 _
        simp
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        change (β.inv ≫ η.hom) ≫ (η.inv ≫ β.hom) = 𝟙 _
        simp }

private theorem tensorSheafCoordinates_unit (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (tensorUnit φ F) ≫
      (tensorSheafCoordinates φ d e F).hom.val = (tensorCoordinates φ d e F).hom := by
  have := tensorUnit_isIso φ d e F
  let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
  let η := Q.mapIso (asIso (tensorUnit φ F))
  unfold tensorSheafCoordinates
  change η.hom ≫ (η.inv ≫ (tensorCoordinates φ d e F).hom) = _
  exact η.hom_inv_id_assoc _

@[irreducible] private def tensorCoordinateIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S))) :
    tensorFunctor φ ⋙ restrictScalars.{u} (𝓻 φ) ≅
      Functor.pi' (fun _ : Fin d ↦ 𝟭 (SheafOfModules.{u} (𝓡 R))) ⋙ Pi.functor (Fin d) :=
  NatIso.ofComponents (tensorSheafCoordinates φ d e) (by
    intro F G f
    apply SheafOfModules.hom_ext
    have := tensorUnit_isIso φ d e F
    let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
    apply (cancel_epi (Q.map (tensorUnit φ F))).1
    change Q.map (tensorUnit φ F) ≫
        (Q.map ((tensorFunctor φ).map f).val ≫
          (tensorSheafCoordinates φ d e G).hom.val) =
      Q.map (tensorUnit φ F) ≫
        ((tensorSheafCoordinates φ d e F).hom.val ≫
          (Limits.Pi.map (fun _ : Fin d ↦ f)).val)
    calc
      _ = (Q.map (tensorUnit φ F) ≫ Q.map ((tensorFunctor φ).map f).val) ≫
          (tensorSheafCoordinates φ d e G).hom.val := (Category.assoc _ _ _).symm
      _ = (Q.map ((tensorPresheafFunctor φ).map f) ≫ Q.map (tensorUnit φ G)) ≫
          (tensorSheafCoordinates φ d e G).hom.val := by
        have hn := congrArg Q.map (tensorUnit_naturality φ f).symm
        simp only [Functor.map_comp] at hn
        exact congrArg (fun k ↦ k ≫ (tensorSheafCoordinates φ d e G).hom.val) hn
      _ = Q.map ((tensorPresheafFunctor φ).map f) ≫
          (tensorCoordinates φ d e G).hom := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun k ↦ Q.map ((tensorPresheafFunctor φ).map f) ≫ k)
            (tensorSheafCoordinates_unit φ d e G))
      _ = (tensorCoordinates φ d e F).hom ≫
          (Limits.Pi.map (fun _ : Fin d ↦ f)).val :=
        tensorCoordinates_naturality φ d e f
      _ = _ := ((congrArg (fun k ↦ k ≫ (Limits.Pi.map (fun _ : Fin d ↦ f)).val)
        (tensorSheafCoordinates_unit φ d e F)).symm).trans (Category.assoc _ _ _))

private theorem power_exact (D : Type*) [Category D] [Abelian D] (d : ℕ) :
    PreservesFiniteLimits
        (Functor.pi' (fun _ : Fin d ↦ 𝟭 D) ⋙ Pi.functor (Fin d)) ∧
      PreservesFiniteColimits
        (Functor.pi' (fun _ : Fin d ↦ 𝟭 D) ⋙ Pi.functor (Fin d)) := by
  let : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  let T := Functor.pi' (fun _ : Fin d ↦ 𝟭 D) ⋙ Pi.functor (Fin d)
  let L := Functor.const (Discrete (Fin d)) ⋙ lim (J := Discrete (Fin d)) (C := D)
  let Q := Functor.const (Discrete (Fin d)) ⋙ colim (J := Discrete (Fin d)) (C := D)
  let e : L ≅ T := NatIso.ofComponents
    (fun M ↦ (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj M)).symm) (by
    intro X Y f
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc]
    change limMap ((Functor.const (Discrete (Fin d))).map f) ≫
        (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj Y)).inv ≫ Pi.π _ i =
      (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj X)).inv ≫
        Limits.Pi.map (fun _ : Fin d ↦ f) ≫ Pi.π _ i
    rw [Pi.isoLimit_inv_π, Pi.map_π, ← Category.assoc, Pi.isoLimit_inv_π, limMap_π]
    rfl)
  have : PreservesFiniteLimits L := inferInstance
  have : PreservesFiniteColimits Q := inferInstance
  let e' : Q ≅ T := Functor.isoWhiskerLeft _
    (HasBiproductsOfShape.colimIsoLim (J := Fin d) (C := D)) ≪≫ e
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e'⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem restriction_limits (α : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  have : PreservesFiniteLimits (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α) ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{u} B))
  have : ReflectsFiniteLimits (toSheaf.{u} A) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms (toSheaf.{u} A)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf A)

private theorem restriction_colimits (α : R ⟶ S) :
    PreservesFiniteColimits (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  have : PreservesFiniteColimits (toSheaf.{u} A) := inferInstance
  have : ReflectsFiniteColimits (toSheaf.{u} A) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms (toSheaf.{u} A)
  have : PreservesFiniteColimits (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α) ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{u} B))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (toSheaf A)

-- The long conjunction repeatedly elaborates sectionwise products and scalar restrictions.
end SheafOfModules
