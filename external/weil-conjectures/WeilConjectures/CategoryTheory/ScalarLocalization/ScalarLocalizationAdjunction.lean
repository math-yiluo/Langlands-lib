/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Adjunctions after localizing the Hom modules

Source: blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`, final sentence.
Tensoring the linear adjunction bijections gives the adjunction after inverting ell.
(blueprint: lem-sfb-scalar-localization-adjunction)

## Main definitions

- `CategoryTheory.ScalarLocalization.transportAdjunction`: a linear adjunction `F ⊣ G` induces
  `transport R p F ⊣ transport R p G`.

## Main statements

- `CategoryTheory.ScalarLocalization.isLeftAdjoint_transport`: a linear left adjoint remains a
  left adjoint after scalar localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe r u v u' v'

open TensorProduct

namespace CategoryTheory.ScalarLocalization

variable (R : Type r) [CommRing R] (p : R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]

/-- A linear adjunction `F ⊣ G` induces an adjunction between the scalar localizations
`transport R p F ⊣ transport R p G`. The Hom bijections are the base changes of the
original ones, so `a ⊗ f` corresponds to `a ⊗ adj.homEquiv f`.
Source: blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`, final sentence
(blueprint: lem-sfb-scalar-localization-adjunction).

Proof: tensor each linear adjunction bijection with the localized coefficient ring.
Naturality in both variables is checked on two pure tensors, where it is the original
adjunction naturality, and then on sums by bilinearity. -/
def transportAdjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] :
    transport R p F ⊣ transport R p G :=
  let e (X : ScalarLocalization R C p) (Y : ScalarLocalization R D p) :
      (Localization.Away p ⊗[R] (F.obj X.obj ⟶ Y.obj)) ≃ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (X.obj ⟶ G.obj Y.obj)) :=
    LinearEquiv.baseChange R (Localization.Away p) _ _
      { adj.homAddEquiv X.obj Y.obj with
        map_smul' := fun a f ↦ by
          change adj.homEquiv _ _ (a • f) = a • adj.homEquiv _ _ f
          simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul] }
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ (e X Y).toEquiv
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        change (e X Y).symm (composition R C p _ _ _ g f) =
          composition R D p _ _ _ ((e X' Y).symm g) (transportHom R p F _ _ f)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          induction g using TensorProduct.inductionOn with
          | tmul b g =>
            change (e X Y).symm (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
            simp only [composition_tmul, e]
            change (b * a) ⊗ₜ[R] (adj.homEquiv _ _).symm (f ≫ g) =
              composition R D p _ _ _ (b ⊗ₜ[R] (adj.homEquiv _ _).symm g)
                (a ⊗ₜ[R] F.map f)
            rw [composition_tmul, adj.homEquiv_naturality_left_symm]
          | add g h hg hh => simp only [map_add, LinearMap.add_apply, hg, hh]
        | add f h hf hh => simp only [map_add, hf, hh]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        change e X Y' (composition R D p _ _ _ h g) =
          composition R C p _ _ _ (transportHom R p G _ _ h) (e X Y g)
        induction g using TensorProduct.inductionOn with
        | tmul a g =>
          induction h using TensorProduct.inductionOn with
          | tmul b h =>
            change e X Y' (composition R D p _ _ _ (b ⊗ₜ[R] h) (a ⊗ₜ[R] g)) = _
            simp only [composition_tmul, e]
            change (b * a) ⊗ₜ[R] adj.homEquiv _ _ (g ≫ h) =
              composition R C p _ _ _ (b ⊗ₜ[R] G.map h)
                (a ⊗ₜ[R] adj.homEquiv _ _ g)
            rw [composition_tmul, adj.homEquiv_naturality_right]
          | add h i hh hi => simp only [map_add, LinearMap.add_apply, hh, hi]
        | add g i hg hi => simp only [map_add, hg, hi] }

/-- A linear left adjoint remains a left adjoint after scalar localization.
Source: blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`, final sentence
(blueprint: lem-sfb-scalar-localization-adjunction).

Proof: the right adjoint is additive and linear, so `transportAdjunction` applies. This does
not assert any geometric comparison or existence of an integral adjoint. -/
theorem isLeftAdjoint_transport (F : C ⥤ D) [F.Additive] [F.Linear R]
    [F.IsLeftAdjoint] : (transport R p F).IsLeftAdjoint := by
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  let := adj.right_adjoint_additive
  let := adj.right_adjoint_linear (R := R)
  exact (transportAdjunction R p adj).isLeftAdjoint

end CategoryTheory.ScalarLocalization
