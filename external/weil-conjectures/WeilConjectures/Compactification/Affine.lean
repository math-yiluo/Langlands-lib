/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Constructions
public import WeilConjectures.Compactification.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!

# Compactification of a quasi-affine scheme of finite type over a base

A quasi-affine scheme `X` that is locally of finite type over `S` admits an immersion
`i : X ⟶ 𝔸(n; S)` into a relative affine space over `S` (Stacks Tag 04II). Composing `i`
with the standard chart `𝔸(n; S) ⟶ ℙ(Option n; S)`, which is an open immersion, exhibits the
structure morphism `X ⟶ S` as an immersion into a scheme proper over `S`. Closing `X` up
inside `ℙ(Option n; S)` therefore compactifies `X ⟶ S`.

This is the base case of the Nagata compactification theorem: it applies in particular when
`X` is affine, which is the situation in which it is used, since the induction of Nagata's
proof starts from an affine open of the scheme to be compactified.

## Main definitions

- `AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`: the compactification of
  `f : X ⟶ S` obtained from an immersion of `X` into a relative affine space over `S`,
  namely the closure of `X` in the relative projective space.

## Main results

- `AlgebraicGeometry.HasCompactification.affineSpace_over`: the projection `𝔸(n; S) ⟶ S` is
  compactifiable for finite `n`.
- `AlgebraicGeometry.HasCompactification.of_isQuasiAffine`: a quasi-compact, locally of
  finite type morphism `f : X ⟶ S` with `X` quasi-affine admits a compactification. In
  particular this holds for `X` affine, and the hypothesis `QuasiCompact f` is automatic as
  soon as `S` is quasi-separated.

## Blueprint

This file implements `def:nagata-affine-compactification` and
`prop:nagata-affine-compactification` of the Nagata compactification blueprint.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **The affine compactification construction**: given an immersion `i : X ⟶ 𝔸(n; S)` of
`X` into a relative affine space over `S` compatible with `f : X ⟶ S`, composing `i` with
the standard chart `𝔸(n; S) ⟶ ℙ(Option n; S)` and closing up the image compactifies `f`.
(blueprint: `def:nagata-affine-compactification`) -/
noncomputable def Compactification.ofIsImmersionAffineSpace {n : Type u} [Finite n]
    {f : X ⟶ S} (i : X ⟶ 𝔸(n; S)) [IsImmersion i] [QuasiCompact f]
    (hi : i ≫ 𝔸(n; S) ↘ S = f) : Compactification f :=
  have hfac : (i ≫ AffineSpace.toRelativeProjectiveSpace n S) ≫ ℙ(Option n; S) ↘ S = f := by
    rw [Category.assoc, AffineSpace.toRelativeProjectiveSpace_over, hi]
  have : QuasiCompact ((i ≫ AffineSpace.toRelativeProjectiveSpace n S) ≫ ℙ(Option n; S) ↘ S) :=
    hfac ▸ ‹QuasiCompact f›
  have : QuasiCompact (i ≫ AffineSpace.toRelativeProjectiveSpace n S) :=
    .of_comp _ (ℙ(Option n; S) ↘ S)
  (Compactification.ofIsImmersion (i ≫ AffineSpace.toRelativeProjectiveSpace n S)
    (ℙ(Option n; S) ↘ S)).copy hfac.symm

/-- **A quasi-affine scheme of finite type over `S` is compactifiable over `S`**
(blueprint: `prop:nagata-affine-compactification`).

Since an affine scheme is quasi-affine, this covers the case of an affine `X` used in the
induction of Nagata's theorem. -/
theorem HasCompactification.of_isQuasiAffine (f : X ⟶ S) [X.IsQuasiAffine]
    [LocallyOfFiniteType f] [QuasiCompact f] : HasCompactification f := by
  obtain ⟨n, i, hi, hii⟩ := exists_immersion_affineSpace_of_quasiAffine f
  exact (Compactification.ofIsImmersionAffineSpace i hi).hasCompactification

/-- The projection of relative affine space in finitely many coordinates is compactifiable, by
its open immersion into relative projective space. -/
instance HasCompactification.affineSpace_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    HasCompactification (𝔸(n; S) ↘ S) :=
  (Compactification.ofIsImmersionAffineSpace (𝟙 _) (Category.id_comp _)).hasCompactification

end AlgebraicGeometry
