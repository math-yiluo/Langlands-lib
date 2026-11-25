/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DualBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace

/-!
# Dual base change: pasting compatibilities

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-thm-sf-compatibility/thm-sf-dual-base-change.md`,
node `definition-trace-morphism--1` (blueprint: definition-trace-morphism--1).

The dual base change isomorphism `Rf^! Rg_* ≅ Rg'_* Rf'^!` is the existing
`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeIso` (the inverse conjugate
of the compact-support exchange `Ex_!`, invertible by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), and its proper form is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerShriekBaseChangeIso`. This file states the
remaining clauses of the node: compatibility of that isomorphism with horizontal and vertical
pasting of Cartesian squares, with respect to the canonical compositors
`AlgebraicGeometry.Etale.rightDerivedLowerStarComp` and the exceptional compositor
`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIsoOfLowerShriek` conjugate to
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- Horizontal pasting for dual base change: for Cartesian squares `sq` (along `g`) and `sq₂`
(along `g₂`), the dual base change isomorphism of the pasted square `sq₂.paste_horiz sq` is the
pasting of those of `sq` and `sq₂`, using the canonical direct-image compositors
`rightDerivedLowerStarComp` (blueprint: `definition-trace-morphism--1`, step 4). -/
def DualBaseChangeHorizontalPasting {X₂ Y₂ : Scheme.{u}} {g₂ : Y₂ ⟶ Y'} {g₂' : X₂ ⟶ X'}
    {f₂ : X₂ ⟶ Y₂} [HasCompactification f₂] [QuasiCompact f₂]
    (sq : IsPullback g' f' f g) (sq₂ : IsPullback g₂' f₂ f' g₂) : Prop :=
  rightDerivedUpperShriekLowerStarBaseChangeIso Λ (sq₂.paste_horiz sq) =
    Functor.isoWhiskerRight (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g₂ g).symm
        R(f)^![Λ] ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft R((g₂)_*[ModuleCat.{u + 1} Λ])
        (rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq₂)
        R((g')_*[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R(f₂)^![Λ] (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g₂' g')

/-- Vertical pasting for dual base change: for a Cartesian square `t` stacked on top of `sq`,
the dual base change isomorphism of the pasted square `t.paste_vert sq` is the pasting of those
of `t` and `sq`, using the exceptional compositors conjugate to `rightDerivedLowerShriekCompIso`
(blueprint: `definition-trace-morphism--1`, step 4). -/
def DualBaseChangeVerticalPasting {X₀ X₀' : Scheme.{u}} {e : X₀ ⟶ X} {g₀' : X₀' ⟶ X₀}
    {f₀' : X₀' ⟶ X'} [HasCompactification e] [HasCompactification (e ≫ f)]
    [QuasiCompact (e ≫ f)] [HasCompactification f₀'] [QuasiCompact f₀']
    [HasCompactification (f₀' ≫ f')] [QuasiCompact (f₀' ≫ f')]
    (sq : IsPullback g' f' f g) (t : IsPullback g₀' f₀' e g') : Prop :=
  rightDerivedUpperShriekLowerStarBaseChangeIso Λ (t.paste_vert sq) ≪≫
      Functor.isoWhiskerRight
        (rightDerivedUpperShriekCompIsoOfLowerShriek Λ f₀' f'
          (rightDerivedLowerShriekCompIso Λ f₀' f')).symm
        R((g₀')_*[ModuleCat.{u + 1} Λ]) =
    Functor.isoWhiskerLeft R((g)_*[ModuleCat.{u + 1} Λ])
        (rightDerivedUpperShriekCompIsoOfLowerShriek Λ e f
          (rightDerivedLowerShriekCompIso Λ e f)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq) R(e)^![Λ] ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R(f')^![Λ] (rightDerivedUpperShriekLowerStarBaseChangeIso Λ t)

/-- Dual base change in the finite-coefficient unbounded datum: compatibility of the dual base
change isomorphism `rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq : Rf^! Rg_* ≅ Rg'_* Rf'^!`
with horizontal and vertical pasting of Cartesian squares, and stability of properness of `g`
under the base change, which is what makes the proper form
`rightDerivedUpperShriekLowerShriekBaseChangeIso` applicable.

Source place: node `definition-trace-morphism--1` in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-proper-pushforward/
sk-thm-sf-compatibility/thm-sf-dual-base-change.md`
(blueprint: definition-trace-morphism--1).

Proof outline: the exchange `Ex_!` is invertible (A2), the dual isomorphism is its inverse
conjugate under the composite A1 adjunctions, and the pasting equations follow from mate
calculus applied to the pasting compatibility of `Ex_!` with the direct-image and compactly
supported compositors. -/
theorem dualBaseChange (sq : IsPullback g' f' f g) :
    (∀ {X₂ Y₂ : Scheme.{u}} {g₂ : Y₂ ⟶ Y'} {g₂' : X₂ ⟶ X'} {f₂ : X₂ ⟶ Y₂}
      [HasCompactification f₂] [QuasiCompact f₂] (sq₂ : IsPullback g₂' f₂ f' g₂),
      DualBaseChangeHorizontalPasting Λ sq sq₂) ∧
    (∀ {X₀ X₀' : Scheme.{u}} {e : X₀ ⟶ X} {g₀' : X₀' ⟶ X₀} {f₀' : X₀' ⟶ X'}
      [HasCompactification e] [HasCompactification (e ≫ f)] [QuasiCompact (e ≫ f)]
      [HasCompactification f₀'] [QuasiCompact f₀']
      [HasCompactification (f₀' ≫ f')] [QuasiCompact (f₀' ≫ f')]
      (t : IsPullback g₀' f₀' e g'),
      DualBaseChangeVerticalPasting Λ sq t) ∧
    (IsProper g → IsProper g') := by
  sorry

end AlgebraicGeometry.Etale
