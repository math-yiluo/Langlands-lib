/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteNestedExtensionMap

/-! # The extension counit of a subterminal object is monic

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ.
(blueprint: lem-dla1-site-subterminal-module-counit-mono)
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

open SubterminalLocal

open Classical in
private theorem counit_summand
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) (Z : C) (F : Modules.{c, v, r} R)
    (T : C) (a : T ⟶ Z) (x : F.val.obj (op T)) :
    ((adj.{c, v, r} R Z).counit.app F).val.app (op T)
      (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (J := J) (R := coefficients.{c, v, r} R)
          (𝟙 (coefficients.{c, v, r} R).obj)).unit.app
            ((extensionByZeroPresheaf.{max c v r} (coefficients.{c, v, r} R) Z).obj
              ((jstar.{c, v, r} R Z).obj F))).app (op T)
        (DirectSum.of (fun b : T ⟶ Z ↦
          ((jstar.{c, v, r} R Z).obj F).val.obj (op (Over.mk b))) a x)) = x := by
  have hη := (localizedSystemAdjunction_existsUnique.{c, v, r} R Z).exists.choose_spec
    ((jstar.{c, v, r} R Z).obj F) (op (Over.mk a)) x
  have ht := congrArg (fun k ↦ k.val.app (op (Over.mk a)) x)
    ((adj.{c, v, r} R Z).right_triangle_components F)
  change ((adj.{c, v, r} R Z).counit.app F).val.app (op T)
    (((adj.{c, v, r} R Z).unit.app ((jstar.{c, v, r} R Z).obj F)).val.app
      (op (Over.mk a)) x) = x at ht
  erw [hη] at ht
  exact ht

private theorem counit_transpose_mono
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) {X Z : C}
    (hX : IsTerminal X) (z : Z ⟶ X) [Mono z] (F : Modules.{c, v, r} R) :
    Mono (((PresheafOfModules.sheafificationAdjunction.{max c v r}
      (J := J) (R := coefficients.{c, v, r} R)
      (𝟙 (coefficients.{c, v, r} R).obj)).homEquiv _ F)
        ((adj.{c, v, r} R Z).counit.app F)) := by
  classical
  let a := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (J := J) (R := coefficients.{c, v, r} R) (𝟙 (coefficients.{c, v, r} R).obj)
  let f := (a.homEquiv _ F) ((adj.{c, v, r} R Z).counit.app F)
  change Mono f
  apply PresheafOfModules.mono_of_injective
  intro T
  let : Subsingleton (T.unop ⟶ Z) := ⟨fun b d ↦
    (cancel_mono z).1 (hX.hom_ext (b ≫ z) (d ≫ z))⟩
  let : DecidableEq (T.unop ⟶ Z) := fun b d ↦ Classical.propDecidable (b = d)
  have hm (b : T.unop ⟶ Z) (x : F.val.obj T) :
      f.app T (DirectSum.of (fun d : T.unop ⟶ Z ↦
        ((jstar.{c, v, r} R Z).obj F).val.obj (op (Over.mk d))) b x) = x := by
    change (((a.homEquiv _ F) ((adj.{c, v, r} R Z).counit.app F)).app T) _ = x
    rw [Adjunction.homEquiv_unit]
    simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply,
      CategoryTheory.Functor.comp_map]
    change ((adj.{c, v, r} R Z).counit.app F).val.app T
      (((a.unit.app ((extensionByZeroPresheaf.{max c v r}
        (coefficients.{c, v, r} R) Z).obj ((jstar.{c, v, r} R Z).obj F))).app T)
          (DirectSum.of (fun d : T.unop ⟶ Z ↦
            ((jstar.{c, v, r} R Z).obj F).val.obj (op (Over.mk d))) b x)) = x
    exact counit_summand.{c, v, r} R Z F T.unop b x
  by_cases hi : Nonempty (T.unop ⟶ Z)
  · let b := hi.some
    have hd (x : ((extensionByZeroPresheaf.{max c v r}
        (coefficients.{c, v, r} R) Z).obj ((jstar.{c, v, r} R Z).obj F)).obj T) :
        DirectSum.of (fun d : T.unop ⟶ Z ↦
          ((jstar.{c, v, r} R Z).obj F).val.obj (op (Over.mk d))) b (f.app T x) = x := by
      induction x using DirectSum.induction_on with
      | zero =>
        change DirectSum.of (fun d : T.unop ⟶ Z ↦
          ((jstar.{c, v, r} R Z).obj F).val.obj (op (Over.mk d))) b
            ((f.app T).hom 0) = 0
        rw [map_zero, map_zero]
      | of d x =>
        obtain rfl : d = b := Subsingleton.elim _ _
        rw [hm]
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    intro x y h
    rw [← hd x, ← hd y, h]
  · let : IsEmpty (T.unop ⟶ Z) := ⟨fun b ↦ hi ⟨b⟩⟩
    intro x y _
    apply DirectSum.ext
    intro b
    exact isEmptyElim b

/-- Extension of restriction along a subterminal object has a monic counit.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(blueprint: lem-dla1-site-subterminal-module-counit-mono).

Proof: transpose the extension counit through the module sheafification
adjunction. The prescribed summand-inclusion formula for the localized unit,
together with the right triangle identity, shows that this presheaf morphism
sends every direct-sum generator to the original section. Terminality of X and
cancellation against Z → X make Hom(T,Z) a subsingleton. If it is inhabited,
direct-sum induction shows that inclusion at its unique index is a left inverse
to the transposed counit. If it is empty, the direct sum is a subsingleton.
Thus the transpose is injective on every object and is a presheaf monomorphism.
Module sheafification preserves monomorphisms, and its counit at a sheaf is
invertible. The inverse hom-equivalence formula expresses the extension
counit as the composite of the sheafified transpose with this invertible
counit. Consequently it is monic. -/
theorem siteSubterminalModuleCounitMono
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) {X Z : C}
    (hX : IsTerminal X) (z : Z ⟶ X) [Mono z] (F : Modules.{c, v, r} R) :
    Mono ((adj.{c, v, r} R Z).counit.app F) := by
  let a := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (J := J) (R := coefficients.{c, v, r} R) (𝟙 (coefficients.{c, v, r} R).obj)
  have : Mono ((a.homEquiv _ F) ((adj.{c, v, r} R Z).counit.app F)) :=
    counit_transpose_mono.{c, v, r} R hX z F
  have hm : Mono ((PresheafOfModules.sheafification.{max c v r}
      (J := J) (R := coefficients.{c, v, r} R) (𝟙 (coefficients.{c, v, r} R).obj)).map
        ((a.homEquiv _ F) ((adj.{c, v, r} R Z).counit.app F)) ≫ a.counit.app F) :=
    inferInstance
  erw [← a.homEquiv_counit, Equiv.symm_apply_apply] at hm
  exact hm

end SheafOfModules
