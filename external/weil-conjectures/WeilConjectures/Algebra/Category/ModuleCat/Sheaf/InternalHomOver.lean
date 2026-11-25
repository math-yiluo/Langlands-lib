/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Restricting the internal hom of sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)` and `U : C`. For sheaves of modules
`M` and `N` over `R`, the restriction of the internal hom `homObj M N` to `Over U` is the internal
hom of the restrictions (`SheafOfModules.overHomObjIso`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}

variable (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
  (U : C)

-- `rfl` would also prove this, but the unifier is very slow on it.
lemma homObj_restrictOver_eq :
    PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
        ((PresheafOfModules.restrictOver R.obj U).obj M.val)
        ((PresheafOfModules.restrictOver R.obj U).obj N.val) =
      PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj) (M.over U).val (N.over U).val := by
  congr 1

/-- **Restricting the internal hom.** The restriction of `homObj M N` to `Over U` is the internal
hom of the restrictions of `M` and `N` to `Over U`. -/
noncomputable def overHomObjIso :
    (homObj M N).over U ≅ homObj (R := R.over U) (M.over U) (N.over U) :=
  (fullyFaithfulForget _).preimageIso <|
    (Iso.refl _ : ((homObj M N).over U).val ≅
      (PresheafOfModules.restrictOver R.obj U).obj (homObj M N).val) ≪≫
    PresheafOfModules.restrictOverHomObjIso (R := R.obj) M.val N.val U ≪≫
    eqToIso (homObj_restrictOver_eq M N U)

end SheafOfModules
