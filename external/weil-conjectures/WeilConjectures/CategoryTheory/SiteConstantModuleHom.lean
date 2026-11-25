/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import WeilConjectures.CategoryTheory.Sites.ConstantForget

/-! # Internal Hom of constant module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T (1), and Tag 0E8H
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical identification of the constant ring sheaf with the underlying ring sheaf
of the constant commutative ring sheaf. Source: Stacks Tags 03CY and 093T
(auxiliary; not a blueprint node). -/
def constantModuleHomRingIso :
    (constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ) ≅
      (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
        ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ)) :=
  letI : J.PreservesSheafification
      (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
    GrothendieckTopology.instPreservesSheafification J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      (FD := fun A B : CommRingCat.{max u v} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u v} ↦ A)
      (FE := fun A B : RingCat.{max u v} ↦ A →+* B)
      (CE := fun A : RingCat.{max u v} ↦ A)
  (sheafComposeNatIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    (sheafificationAdjunction J CommRingCat.{max u v})
    (sheafificationAdjunction J RingCat.{max u v})).app
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))

/-- The recorded constant-module functor, transported along the canonical ring isomorphism
so that the recorded internal Hom applies. Source: Stacks Tags 03CY and 093T
(auxiliary; not a blueprint node). -/
def constantModuleHomFunctor :
    ModuleCat.{max u v} Λ ⥤ SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
        ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ))) :=
  siteConstantModuleFunctorGeneral J Λ ⋙
    SheafOfModules.pushforward (F := 𝟭 C) (constantModuleHomRingIso J Λ).inv

/-- The constant-section unit, retaining the underlying additive sheafification unit after
canonical coefficient transport. Source: Stacks Tags 03CY and 093T
(auxiliary; not a blueprint node). -/
def constantModuleHomUnit (M : ModuleCat.{max u v} Λ) :
    (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M) ⟶
      ((constantModuleHomFunctor J Λ).obj M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf

private instance homUnit_surjective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallySurjective J (constantModuleHomUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private instance homUnit_injective (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallyInjective J (constantModuleHomUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

end CategoryTheory
