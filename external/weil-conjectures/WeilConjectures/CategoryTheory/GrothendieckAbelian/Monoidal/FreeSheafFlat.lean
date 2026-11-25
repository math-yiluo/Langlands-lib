/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Flatness of the sheafified free presheaf

Source: literature/stacks-project/sites-modules.tex, Lemma 03EV.

## Main statement

The sheaf associated to the free presheaf on a representable, with a flat
coefficient object, is flat.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A]

/--
The sheafification of the free presheaf on a representable with flat
coefficient object is flat, expressed as preservation of finite limits by
left tensoring. This is Lemma 03EV of the Stacks Project, generalized to
Grothendieck abelian symmetric monoidal closed coefficient categories.
Source: Stacks Project, Modules on Sites, Lemmas 03EV, 03ES, 03ET and 0GMW;
the coefficient-category generalization is described in the module docstring of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.

Proof:
1. Put `Q = Presheaf.freeYoneda X P`, and write `a` for sheafification and
   `iota` for the sheaf inclusion. Strong monoidality of `a`
   [lem-weil-pbc-sheaf-tensor-closed] (2), together with the counit isomorphism
   [situation-conventions] (3), gives a natural
   isomorphism from tensoring with `a Q` to `iota` followed by tensoring with
   `Q` and then `a`. It suffices to show that this composite is left exact.
2. For each `V`, `Q(V)` is the coproduct of copies of `P` indexed by `V ⟶ X`.
   Each copy is flat by `hP`, and the coproduct is flat by
   [lem-weil-pbc-flat-coproduct]: closedness makes tensor preserve coproducts,
   and AB4, implied by the Grothendieck AB5 condition, makes coproducts exact.
   This includes the empty coproduct, which is zero.
3. Evaluation preserves finite limits, and finite limits of presheaves are
   computed objectwise [situation-conventions] (1).
   Evaluation of tensoring with `Q` is evaluation followed by tensoring with
   the flat object `Q(V)` from step 2, so tensoring with `Q` is left exact.
4. The inclusion `iota` preserves finite limits
   [situation-conventions] (2), and `a` is exact
   [lem-weil-pbc-sheaf-tensor-closed] (1). The composite in step 1 therefore
   preserves finite limits; transport along its natural isomorphism proves
   the conclusion.

In Lean, steps 1, 3 and 4 are `flat_presheafToSheaf_obj`; the proof below only
carries out step 2.
-/
lemma free_sheaf_flat (P : A) (hP : PreservesFiniteLimits (tensorLeft P))
    (X : C) :
    PreservesFiniteLimits (tensorLeft (Sheaf.freeYoneda J X P)) := by
  -- Retain the additivity hypothesis in the existing theorem interface.
  have _hadd : MonoidalPreadditive A := inferInstance
  apply (ObjectProperty.flat_iff_preservesFiniteLimits _).1
  change ObjectProperty.flat ((presheafToSheaf J A).obj (Presheaf.freeYoneda X P))
  apply flat_presheafToSheaf_obj A J
  intro V
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} A
    (ULift.{u + 1} (V.unop ⟶ X))
  exact ObjectProperty.prop_of_iso _
    (Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} (V.unop ⟶ X) ↦ P) Equiv.ulift
      fun _ ↦ Iso.refl P)
    (ObjectProperty.flat_coproduct _ fun _ ↦
      (ObjectProperty.flat_iff_preservesFiniteLimits P).2 hP)

end CategoryTheory.GrothendieckTopology
