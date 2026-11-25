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
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Compatible coefficient tensor towers

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CY and 03DA;
Homology, Tag 011G (blueprint: lem-pur-compatible-coefficient-tower).

The natural-number index `n` represents the paper's positive index `n + 1`.
The tensor API writes the coefficient factor first, so `z ⊗ x` below is the
paper's `x ⊗ z`. Generators always mean images under the sheafification unit.
-/

@[expose] public section

universe uC vC u uk

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}

/-- Forget commutativity of the coefficient sheaf, using the existing sheaf-composition
functor. Source: Stacks 03EK (blueprint: lem-pur-compatible-coefficient-tower). -/
abbrev coefficientTensorRing (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {R S : Sheaf J CommRingCat.{u}} {B : ℕ → Sheaf J CommRingCat.{u}}
  (r : ∀ n, R ⟶ B n) (p : ∀ n, S ⟶ B n)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def tensorPreFunctor (a : R ⟶ S) :
    SheafOfModules.{u} (coefficientTensorRing R) ⥤
      PresheafOfModules.{u} (coefficientTensorRing S).obj where
  obj := changeOfRingsPresheaf.{vC, uC, u} a
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{vC, uC, u} a _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private noncomputable def towerPrelevel (n : ℕ) :
    SheafOfModules.{u} (coefficientTensorRing R) ⥤
      PresheafOfModules.{u} (coefficientTensorRing S).obj :=
  tensorPreFunctor (r n) ⋙ PresheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n)).hom

set_option backward.isDefEq.respectTransparency.types true in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorCoefficientSection
    {T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : R ⟶ T) (c : S ⟶ T)
    (h : a ≫ c = d) (M : SheafOfModules.{u} (coefficientTensorRing R)) (U : Cᵒᵖ) :
    (changeOfRingsPresheaf a M).obj U ⟶
      (ModuleCat.restrictScalars (c.hom.app U).hom).obj
        ((changeOfRingsPresheaf d M).obj U) := by
  let : Module (R.obj.obj U) (T.obj.obj U) :=
    Module.compHom (T.obj.obj U) (d.hom.app U).hom
  let N := (ModuleCat.restrictScalars (c.hom.app U).hom).obj
    ((changeOfRingsPresheaf d M).obj U)
  let f : M.val.obj U ⟶ (ModuleCat.restrictScalars (a.hom.app U).hom).obj N :=
    ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (a.hom.app U).hom).obj N)
      { toFun := fun x ↦ (1 : T.obj.obj U) ⊗ₜ[R.obj.obj U, (d.hom.app U).hom] x
        map_add' := by intro x y; simp [TensorProduct.tmul_add]
        map_smul' := by
          intro s x
          have hs : c.hom.app U (a.hom.app U s) = d.hom.app U s :=
            congrArg (fun f : R ⟶ T ↦ f.hom.app U s) h
          change (1 : T.obj.obj U) ⊗ₜ[R.obj.obj U] (s • x) =
            c.hom.app U (a.hom.app U s) •
              ((1 : T.obj.obj U) ⊗ₜ[R.obj.obj U] x)
          rw [hs, TensorProduct.tmul_smul (R' := R.obj.obj U)]
          rfl }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (a.hom.app U).hom f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorCoefficientSection_tmul
    {T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (d : R ⟶ T) (c : S ⟶ T)
    (h : a ≫ c = d) (M : SheafOfModules.{u} (coefficientTensorRing R)) (U : Cᵒᵖ)
    (z : S.obj.obj U) (x : M.val.obj U) :
    tensorCoefficientSection a d c h M U (z ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
      c.hom.app U z ⊗ₜ[R.obj.obj U, (d.hom.app U).hom] x := by
  let : Module (R.obj.obj U) (T.obj.obj U) :=
    Module.compHom (T.obj.obj U) (d.hom.app U).hom
  let N := (ModuleCat.restrictScalars (c.hom.app U).hom).obj
    ((changeOfRingsPresheaf d M).obj U)
  let : Module (R.obj.obj U) N := Module.compHom N (a.hom.app U).hom
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (a.hom.app U).hom
  unfold tensorCoefficientSection
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change c.hom.app U z •
    ((1 : T.obj.obj U) ⊗ₜ[R.obj.obj U, (d.hom.app U).hom] x) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

attribute [local irreducible] tensorCoefficientSection

private theorem tensorAddHom_ext
    {A P Q N : Type*} [CommRing A] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup N]
    [Module A P] [Module A Q] (f g : TensorProduct A P Q →+ N)
    (h : ∀ x y, f (x ⊗ₜ[A] y) = g (x ⊗ₜ[A] y)) : f = g := by
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy => rw [map_add, map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def towerPretransition
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) (n : ℕ)
    (M : SheafOfModules.{u} (coefficientTensorRing R)) :
    (towerPrelevel r p (n + 1)).obj M ⟶ (towerPrelevel r p n).obj M where
  app U := ModuleCat.ofHom
    (X := ((towerPrelevel r p (n + 1)).obj M).obj U)
    (Y := ((towerPrelevel r p n).obj M).obj U)
    { toFun := tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U
      map_add' := map_add _
      map_smul' := by
        intro s x
        have hs : (b n).hom.app U ((p (n + 1)).hom.app U s) = (p n).hom.app U s :=
          congrArg (fun f : S ⟶ B n ↦ f.hom.app U s) (hp n)
        change tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U
          (((p (n + 1)).hom.app U s) •
            (show (changeOfRingsPresheaf.{vC, uC, u} (r (n + 1)) M).obj U from x)) = _
        rw [map_smul]
        change (b n).hom.app U ((p (n + 1)).hom.app U s) •
          (show (changeOfRingsPresheaf.{vC, uC, u} (r n) M).obj U from
            tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U x) = _
        rw [hs]
        rfl }
  naturality {U V} f := by
    suffices h :
        (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M V).hom.toAddMonoidHom.comp
          (changeOfRingsMap (r (n + 1)) M f).hom.toAddMonoidHom =
        (changeOfRingsMap (r n) M f).hom.toAddMonoidHom.comp
          (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U).hom.toAddMonoidHom by
      ext t
      exact DFunLike.congr_fun h t
    apply tensorAddHom_ext
    intro z x
    change tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M V
      (changeOfRingsMap (r (n + 1)) M f (z ⊗ₜ x)) =
        changeOfRingsMap (r n) M f
          (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U (z ⊗ₜ x))
    rw [show changeOfRingsMap (r (n + 1)) M f (z ⊗ₜ x) = _ from
      Classical.choose_spec (exists_changeOfRingsMap (r (n + 1)) M f) z x]
    rw [tensorCoefficientSection_tmul, tensorCoefficientSection_tmul]
    rw [show changeOfRingsMap (r n) M f
      ((b n).hom.app U z ⊗ₜ[R.obj.obj U, ((r n).hom.app U).hom] x) = _ from
      Classical.choose_spec (exists_changeOfRingsMap (r n) M f) ((b n).hom.app U z) x]
    congr 1
    exact ConcreteCategory.congr_hom ((b n).hom.naturality f) z

private theorem towerPretransition_naturality
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) (n : ℕ)
    {M N : SheafOfModules.{u} (coefficientTensorRing R)} (f : M ⟶ N) :
    towerPretransition r p b hr hp n M ≫ (towerPrelevel r p n).map f =
      (towerPrelevel r p (n + 1)).map f ≫ towerPretransition r p b hr hp n N := by
  apply PresheafOfModules.hom_ext
  intro U
  suffices h :
      ((ModuleCat.extendScalars ((r n).hom.app U).hom).map
        (f.val.app U)).hom.toAddMonoidHom.comp
          (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U).hom.toAddMonoidHom =
      (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) N U).hom.toAddMonoidHom.comp
        ((ModuleCat.extendScalars ((r (n + 1)).hom.app U).hom).map
          (f.val.app U)).hom.toAddMonoidHom by
    ext t
    exact DFunLike.congr_fun h t
  apply tensorAddHom_ext
  intro z x
  change (ModuleCat.extendScalars ((r n).hom.app U).hom).map (f.val.app U)
    (tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) M U (z ⊗ₜ x)) =
      tensorCoefficientSection (r (n + 1)) (r n) (b n) (hr n) N U
        ((ModuleCat.extendScalars ((r (n + 1)).hom.app U).hom).map
          (f.val.app U) (z ⊗ₜ x))
  rw [tensorCoefficientSection_tmul]
  erw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul]
  rw [tensorCoefficientSection_tmul]

private noncomputable def towerTransition
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) (n : ℕ) :
    towerPrelevel r p (n + 1) ⋙ PresheafOfModules.sheafification
      (𝟙 (coefficientTensorRing S).obj) ⟶
        towerPrelevel r p n ⋙ PresheafOfModules.sheafification
          (𝟙 (coefficientTensorRing S).obj) where
  app M := (PresheafOfModules.sheafification
    (𝟙 (coefficientTensorRing S).obj)).map (towerPretransition r p b hr hp n M)
  naturality {M N} f := by
    symm
    change (PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).map
      (towerPretransition r p b hr hp n M) ≫
        (PresheafOfModules.sheafification (𝟙 (coefficientTensorRing S).obj)).map
          ((towerPrelevel r p n).map f) = _
    simp only [Functor.comp_map, ← Functor.map_comp]
    rw [towerPretransition_naturality r p b hr hp]

private theorem sheafification_map_unit
    {A : Sheaf J RingCat.{u}} {P Q : PresheafOfModules.{u} A.obj} (f : P ⟶ Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafification (𝟙 A.obj)).map f).val.app U
      ((toSheafify J P.presheaf).app U x) = (toSheafify J Q.presheaf).app U (f.app U x) := by
  exact (congrArg (fun t ↦ t.app U x)
    (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map f))).symm

end SheafOfModules
