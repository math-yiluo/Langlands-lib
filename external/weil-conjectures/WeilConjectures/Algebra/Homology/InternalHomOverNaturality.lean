/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver

/-! # Naturality of internal Hom under restriction

Source: Stacks Project, Modules on Sites, Sections 04TT and 04IX.
(blueprint: lem-sc-internal-hom-over-naturality).
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the internal Hom restriction isomorphism in both arguments.

Source: Stacks Project, Modules on Sites, Section 04TT (internal Hom), and
Definition 04IX (localization); this is the sectionwise comparison underlying
Cohomology Tag 08DL.

Proof: Forget to presheaves of modules and evaluate at W in the opposite of Over U.
A section is a module morphism between restrictions to Over W.left. The forward
comparison sends it to its precomposition with Over.iteratedSliceForward W.
The left side first sends φ to f restricted to W.left composed with φ composed
with g restricted to W.left, and then precomposes this composite. The right side
first precomposes φ and then composes with the twice restricted f and g.
On every object V over W, both expressions act by f at V.left.left, then φ at
V.left.left, then g at V.left.left. Equality of the component linear maps gives
equality of presheaf morphisms; the fully faithful forgetful functor gives equality
of sheaf morphisms. No nonempty-open, finiteness, or boundedness hypothesis is used;
identity maps and zero maps satisfy the same formula.
(blueprint: lem-sc-internal-hom-over-naturality). -/
theorem overHomObjIso_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}} (U : C)
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (SheafOfModules.overFunctor _ U).map
        (SheafOfModules.homObjMap (R := R) f g) ≫
          (SheafOfModules.overHomObjIso A' B' U).hom =
      (SheafOfModules.overHomObjIso A B U).hom ≫
        SheafOfModules.homObjMap (R := R.over U)
          ((SheafOfModules.overFunctor _ U).map f)
          ((SheafOfModules.overFunctor _ U).map g) := by
  apply SheafOfModules.hom_ext
  simp only [SheafOfModules.comp_val, SheafOfModules.overHomObjIso,
    Functor.FullyFaithful.preimageIso_hom, SheafOfModules.fullyFaithfulForget,
    Iso.trans_hom, Iso.refl_hom]
  have he (P Q : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
      (eqToIso (SheafOfModules.homObj_restrictOver_eq P Q U)).hom =
        𝟙 (PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
          (P.over U).val (Q.over U).val) := by
    exact eqToHom_refl
      (PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
        (P.over U).val (Q.over U).val)
      (SheafOfModules.homObj_restrictOver_eq P Q U)
  rw [he, he]
  ext W φ : 3
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  rfl

end CategoryTheory
