/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Compactification.Defs

/-!

# Compactifications constructed from immersions

If `g : X ⟶ Y` is a quasi-compact immersion and `p : Y ⟶ S` is proper, then closing up `X`
inside `Y` compactifies `g ≫ p`: the factorization
```
X ⟶ g.image ⟶ Y ⟶ S
```
through the scheme-theoretic image of `g` exhibits a compactification of `g ≫ p`, since
`X ⟶ g.image` is an open immersion (`g` being a quasi-compact immersion) and
`g.image ⟶ S` is the composite of a closed immersion with the proper morphism `p`.

The application we record is that **compactifiability is inherited by closed subschemes**:
if `i : X ⟶ X'` is a closed immersion and `c` is a compactification of a quasi-compact
`f' : X' ⟶ S`, then `i ≫ c.i : X ⟶ c.Z` is a quasi-compact immersion into a scheme proper
over `S`, so the construction above applies to it and produces a compactification of
`i ≫ f'` whose ambient scheme is the scheme-theoretic image of `X` in `c.Z`.

## Main definitions

- `AlgebraicGeometry.Compactification.ofIsImmersion`: the compactification of `g ≫ p`
  described above;
- `AlgebraicGeometry.Compactification.ofIsClosedImmersion`: the compactification of
  `i ≫ f'` obtained by closing up a closed subscheme `X ⟶ X'` inside a compactification
  of `f'`.

## Main results

- `AlgebraicGeometry.HasCompactification.of_isImmersion`: a quasi-compact morphism that
  factors as an immersion into a scheme proper over the base admits a compactification;
- `AlgebraicGeometry.HasCompactification.of_isClosedImmersion`: if a quasi-compact
  `f' : X' ⟶ S` admits a compactification, then so does its restriction `i ≫ f'` to any
  closed subscheme `i : X ⟶ X'`.

## Blueprint

This file implements `def:nagata-immersion-compactification`,
`lemma:nagata-immersion-into-proper`, `def:nagata-closed-subscheme-compactification` and
`prop:nagata-closed-subscheme-compactifiable` of the Nagata compactification blueprint.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X X' Y S : Scheme.{u}}

/-- **Compactification constructed from an immersion** (blueprint:
`def:nagata-immersion-compactification`, `lemma:nagata-immersion-into-proper`). -/
noncomputable def Compactification.ofIsImmersion (g : X ⟶ Y) (p : Y ⟶ S)
    [IsImmersion g] [QuasiCompact g] [IsProper p] : Compactification (g ≫ p) where
  Z := g.image
  g := g.imageι ≫ p
  i := g.toImage
  comm := (g.toImage_imageι_assoc p).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- A quasi-compact morphism that factors as an immersion into a scheme proper over the
base admits a compactification.
(blueprint: `lemma:nagata-immersion-into-proper`) -/
theorem HasCompactification.of_isImmersion {u : X ⟶ S} (g : X ⟶ Y) (p : Y ⟶ S)
    [IsImmersion g] [IsProper p] [QuasiCompact u] (fac : g ≫ p = u) :
    HasCompactification u := by
  subst fac
  have : QuasiCompact g := .of_comp g p
  exact (Compactification.ofIsImmersion g p).hasCompactification

/-- **Closed-subscheme compactification construction** (blueprint:
`def:nagata-closed-subscheme-compactification`).

The ambient scheme is the scheme-theoretic image of `i ≫ c.i`, and the factorization is
```
X ⟶ (i ≫ c.i).image ⟶ c.Z ⟶ S.
```
-/
noncomputable def Compactification.ofIsClosedImmersion (i : X ⟶ X') {f' : X' ⟶ S}
    (c : Compactification f') [IsClosedImmersion i] [QuasiCompact f'] :
    Compactification (i ≫ f') :=
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  (ofIsImmersion (i ≫ c.i) c.g).copy (by rw [Category.assoc, ← c.comm])

namespace Compactification

variable (i : X ⟶ X') {f' : X' ⟶ S} (c : Compactification f') [IsClosedImmersion i]
  [QuasiCompact f']

@[simp] lemma ofIsClosedImmersion_Z :
    (ofIsClosedImmersion i c).Z = (i ≫ c.i).image := rfl

@[simp] lemma ofIsClosedImmersion_i :
    (ofIsClosedImmersion i c).i = (i ≫ c.i).toImage := rfl

@[simp] lemma ofIsClosedImmersion_g :
    (ofIsClosedImmersion i c).g = (i ≫ c.i).imageι ≫ c.g := rfl

end Compactification

/-- **Compactifiability is inherited by closed subschemes**: if a quasi-compact morphism
`f' : X' ⟶ S` admits a compactification, then so does its restriction `i ≫ f'` to a closed
subscheme `i : X ⟶ X'`.
(blueprint: `prop:nagata-closed-subscheme-compactifiable`) -/
theorem HasCompactification.of_isClosedImmersion (i : X ⟶ X') (f' : X' ⟶ S)
    [IsClosedImmersion i] [QuasiCompact f'] [HasCompactification f'] :
    HasCompactification (i ≫ f') :=
  (Compactification.ofIsClosedImmersion i
    (HasCompactification.compactification f')).hasCompactification

end AlgebraicGeometry
