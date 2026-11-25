/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Flatness of the localized unit extended by zero

Source: Stacks Project, Modules on Sites, Lemma 18.28.7, Tag 03EV, clause (2)
(blueprint: lem-pc-sites-modules-j-shriek-flat).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- The sheafification of the extension-by-zero presheaf of the unit module on `C/U`
is flat over `R`. Before sheafification, the extension-by-zero presheaf at `V` is the
direct sum of copies of `R(V)` indexed by morphisms `V ⟶ U`.

Source: Stacks Project, Modules on Sites, Lemma 18.28.7, Tag 03EV, clause (2)
(blueprint: lem-pc-sites-modules-j-shriek-flat).

Proof:
1. By `def-weil-extension-by-zero-presheaf`, the unit on the localized ringed site
   has extension-by-zero presheaf `P(V) = ⨁ (φ : V ⟶ U), R(V)`. Each section module
   is free and therefore flat, including an empty direct sum. Presheaf tensor products
   and finite limits are computed sectionwise, so tensoring with `P` preserves finite
   limits (Stacks Tag 03ES).
2. By `def-weil-presheaf-modules-sheafification`, the extension-by-zero sheaf is `P^#`.
   Since `R` is already a sheaf, apply `lem-pc-sites-modules-sheafification-flat`
   (Stacks Tag 03ET) to the finite-limit-preserving tensor functor from step 1.
   Tensoring with `P^#` preserves finite limits; tensor is right exact, so this is
   exactness, namely `def-pc-flat-sheaf-modules`. -/
theorem isFlat_extensionByZero_unit
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C) :
    IsFlat ((PresheafOfModules.sheafification.{u}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).obj
        ((extensionByZeroPresheaf.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj
            (unit (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U)))) := by
  classical
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let P := (extensionByZeroPresheaf.{u} O U).obj (unit (O.over U))
  have hflat (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (P.obj V) := by
    change Module.Flat (R.obj.obj V)
      (DirectSum (V.unop ⟶ U) (fun _ => R.obj.obj V))
    infer_instance
  have hP : Limits.PreservesFiniteLimits (MonoidalCategory.tensorRight P) := by
    constructor
    intro K _ _
    have (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (P.obj V) := hflat V
    exact ⟨⟨fun hc => ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V => Limits.isLimitOfPreserves
        (MonoidalCategory.tensorRight (show ModuleCat (R.obj.obj V) from P.obj V))
        (Limits.isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ => Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ => Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj
    (R := R) (𝟙 O.obj) P hP).2

end SheafOfModules
