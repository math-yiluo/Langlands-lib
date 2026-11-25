/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.DirectSum.Finsupp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat

/-!
# Sheaves of modules on a small ringed site

Source: Stacks Project, Cohomology on Sites, Section 07A5; Modules on Sites,
Lemmas 03DA, 03DB and 03EW (blueprint: lem-pur-ringed-site-grothendieck-abelian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (O : Sheaf J CommRingCat.{u})

local notation "R" => Functor.obj (sheafCompose J (forget₂ CommRingCat RingCat)) O

set_option backward.isDefEq.respectTransparency false in
/-- Sectionwise the free Yoneda module and the localized-unit extension are
`(V ⟶ U) →₀ R(V)` and `⨁ (V ⟶ U), R(V)`. The standard linear equivalence
commutes with restrictions because both compose the index and restrict coefficients.
Source: Stacks Project, Modules on Sites, Tag 03DI, explicit direct-sum construction.
(blueprint: lem-pur-ringed-site-grothendieck-abelian). -/
private noncomputable def freeYonedaExtensionIso (U : C) :
    (PresheafOfModules.free (R).obj).obj (yoneda.obj U) ≅
      (extensionByZeroPresheaf R U).obj (unit ((R).over U)) := by
  classical
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · exact (finsuppLEquivDirectSum ((R).obj.obj V) ((R).obj.obj V)
      (V.unop ⟶ U)).toModuleIso
  · intro V W a
    apply ModuleCat.free_hom_ext
    intro φ
    dsimp
    change (finsuppLEquivDirectSum ((R).obj.obj W) ((R).obj.obj W) (W.unop ⟶ U))
        (ModuleCat.freeDesc (M :=
          (ModuleCat.restrictScalars ((R).obj.map a).hom).obj
            ((ModuleCat.free ((R).obj.obj W)).obj (W.unop ⟶ U)))
          (↾fun x ↦ ModuleCat.freeMk (a.unop ≫ x)) (ModuleCat.freeMk φ)) = _
    rw [ModuleCat.freeDesc_apply]
    change (finsuppLEquivDirectSum ((R).obj.obj W) ((R).obj.obj W) (W.unop ⟶ U))
        (Finsupp.single (a.unop ≫ φ) 1) =
      extensionByZeroPresheafRestrictAdd R U (unit ((R).over U)) a
        ((finsuppLEquivDirectSum ((R).obj.obj V) ((R).obj.obj V) (V.unop ⟶ U))
          (Finsupp.single φ 1))
    rw [finsuppLEquivDirectSum_single, finsuppLEquivDirectSum_single]
    change DirectSum.of _ (a.unop ≫ φ) (1 : (R).obj.obj W) =
      extensionByZeroPresheafRestrictAdd R U (unit ((R).over U)) a
        (DirectSum.of _ φ (1 : (R).obj.obj V))
    dsimp [extensionByZeroPresheafRestrictAdd]
    erw [DirectSum.toAddMonoid_of]
    change DirectSum.of (fun _ : W.unop ⟶ U ↦ (R).obj.obj W)
        (a.unop ≫ φ) (1 : (R).obj.obj W) =
      DirectSum.of (fun _ : W.unop ⟶ U ↦ (R).obj.obj W)
        (a.unop ≫ φ) (((R).obj.map a).hom (1 : (R).obj.obj V))
    rw [((R).obj.map a).hom.map_one]


local instance : HasColimitsOfShape (Discrete C) (SheafOfModules.{u} R) := inferInstance

/-- Sheaves of modules over a sheaf of commutative rings on a small site form a
Grothendieck abelian category. A specific generator is the coproduct, over all
objects `U`, of the sheafifications of the extension-by-zero presheaves of
the rank-one module on the localized ringed site.

Source: Stacks Project, Section 07A5 and Lemmas 03DA, 03DB, 03EW
(blueprint: lem-pur-ringed-site-grothendieck-abelian).

Proof:
1. Apply the source library's `SheafOfModules.isGrothendieckAbelian`, which
   proves existence of colimits, exact filtered colimits and a separator.
2. Identify the free Yoneda presheaf at each object with the extension-by-zero
   presheaf of the localized unit using `finsuppLEquivDirectSum`. On basis
   vectors, naturality is precomposition of the index and preservation of `1`
   by the ring restriction. Apply sheafification to this isomorphism.
3. Transport `SheafOfModules.isSeparating_sheafification_freeYoneda` along
   these isomorphisms. A map from a free Yoneda sheaf is precomposed with the
   inverse isomorphism; cancellation of that inverse gives the required
   separating-family equality. Its coproduct is a separator by
   `ObjectProperty.IsSeparating.isSeparator_coproduct`. -/
theorem grothendieckAbelian_with_localized_generator :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) ∧
      IsSeparator (∐ fun U : C ↦
        (PresheafOfModules.sheafification.{u} (𝟙 (R).obj)).obj
          ((extensionByZeroPresheaf.{u} R U).obj (unit ((R).over U)))) := by
  classical
  refine ⟨isGrothendieckAbelian R, ?_⟩
  apply ObjectProperty.IsSeparating.isSeparator_coproduct
  intro M N f g h
  apply isSeparating_sheafification_freeYoneda R f g
  rintro _ ⟨U⟩ a
  let e := (PresheafOfModules.sheafification (𝟙 (R).obj)).mapIso
    (freeYonedaExtensionIso J O U)
  have he := h _ (ObjectProperty.ofObj_apply _ U) (e.inv ≫ a)
  simpa only [Category.assoc, Iso.cancel_iso_inv_left] using he

end SheafOfModules
