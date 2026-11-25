/-
Copyright (c) 2026 Christian Merten, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Compactification.Defs

/-!

# Base change of a compactification

If `c` is a compactification of `p : Y ⟶ T` and `S ⟶ T` is any morphism, the fibre
product of `c` with `S` over `T` compactifies the base change of `p` along `S ⟶ T`:
```
X ×_T S ⟶ c.Z ×_T S ⟶ S.
```
The right hand map is proper because properness is stable under base change, and the left
hand map is an open immersion because it is the base change of `c.i` along
`c.Z ×_T S ⟶ c.Z`.

Since the source of a base change is rarely a literal `CategoryTheory.Limits.pullback` term,
the construction is stated for an arbitrary pullback square `IsPullback h u p t`; the
special case of the literal pullback is `Compactification.baseChange`.

Writing `i'` and `g'` for the open immersion and the proper morphism of `c.ofIsPullback hsq`,
both squares of the pasting
```
X ----h----> Y          c.Z ×_T S --fst--> c.Z
|            |          |                  |
i'          c.i         g'                c.g
v            v          v                  v
c.Z ×_T S --fst--> c.Z  S --------t------> T
```
are Cartesian (`Compactification.isPullback_i_ofIsPullback` and
`Compactification.isPullback_g_ofIsPullback`). This is the geometric input for the base change
morphism of the lower shriek.

## Main definitions

- `AlgebraicGeometry.Compactification.ofIsPullback`: the compactification of `u` obtained by
  base changing a compactification of `p` along a pullback square `IsPullback h u p t`;
- `AlgebraicGeometry.Compactification.baseChange`: the special case of a literal fibre
  product, i.e. the compactification of `pullback.snd f t` obtained from one of `f`.

## Main results

- `AlgebraicGeometry.Compactification.isPullback_of_isPullback`: the open immersion of the
  base changed compactification is a base change of the original open immersion, and
  `AlgebraicGeometry.Compactification.isPullback_i_ofIsPullback` its special case for
  `Compactification.ofIsPullback`;
- `AlgebraicGeometry.Compactification.isPullback_g_ofIsPullback`: the proper morphism of the
  base changed compactification is the base change of the original proper morphism;
- `AlgebraicGeometry.HasCompactification.of_isPullback`: compactifiability is stable under
  base change, with the two projections of a fibre product as instances
  (`AlgebraicGeometry.HasCompactification.pullback_snd` and
  `AlgebraicGeometry.HasCompactification.pullback_fst`);
- `AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_i_ofIsPullback` and
  `AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_i_baseChange`: along a
  **flat** base change, scheme-theoretic density of the open immersion is preserved;
- `AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g_ofIsPullback`: if the
  proper morphism of the compactification is locally of finite presentation, so is its base
  change.

Flatness of the base change morphism is a genuine hypothesis in the density statements: for
an arbitrary base change the pulled back open need not be dense in the pulled back
compactification, and the remedy is to replace it by its schematic closure.

## Blueprint

This file implements `def:nagata-compactification-base-change` and
`lemma:nagata-compactification-base-change` of the Nagata compactification blueprint.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y S T : Scheme.{u}} {u : X ⟶ S} {p : Y ⟶ T} {h : X ⟶ Y} {t : S ⟶ T}

namespace Compactification

/-- **The open immersion of a base-changed compactification is a base change of the
original open immersion.**

The square is obtained by cancelling the defining square of `c.Z ×_T S` off the bottom of
the given square `IsPullback h u p t`. -/
theorem isPullback_of_isPullback (hsq : IsPullback h u p t) (c : Compactification p)
    {i : X ⟶ pullback c.g t} (hfst : i ≫ pullback.fst c.g t = h ≫ c.i)
    (hsnd : i ≫ pullback.snd c.g t = u) :
    IsPullback h i c.i (pullback.fst c.g t) :=
  .of_bot (by rw [hsnd, ← c.comm]; exact hsq) hfst.symm (.of_hasPullback c.g t)

/-- **Base change construction for a compactification** (blueprint:
`def:nagata-compactification-base-change`,
`lemma:nagata-compactification-base-change`). -/
@[simps]
noncomputable def ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) :
    Compactification u where
  Z := pullback c.g t
  g := pullback.snd c.g t
  i := pullback.lift (h ≫ c.i) u (by rw [Category.assoc, ← c.comm, hsq.w])
  comm := (pullback.lift_snd _ _ _).symm
  isProper := inferInstance
  isOpenImmersion :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_of_isPullback hsq c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))
      c.isOpenImmersion

/-- **The open immersion of a base-changed compactification is a base change of the
original open immersion**, for the compactification `c.ofIsPullback hsq`:

```
  X ----h----------------> Y
  |                        |
  (c.ofIsPullback hsq).i   c.i
  ↓                        ↓
  c.Z ×_T S --fst-------> c.Z
```
-/
theorem isPullback_i_ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) :
    IsPullback h (c.ofIsPullback hsq).i c.i (pullback.fst c.g t) :=
  isPullback_of_isPullback hsq c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The open immersion of `c.ofIsPullback hsq` followed by the projection to `c.Z` is
`h ≫ c.i`. -/
@[reassoc (attr := simp)]
lemma ofIsPullback_i_fst (hsq : IsPullback h u p t) (c : Compactification p) :
    (c.ofIsPullback hsq).i ≫ pullback.fst c.g t = h ≫ c.i :=
  pullback.lift_fst _ _ _

/-- The open immersion of `c.ofIsPullback hsq` followed by the projection to `S` is `u`. -/
@[reassoc (attr := simp)]
lemma ofIsPullback_i_snd (hsq : IsPullback h u p t) (c : Compactification p) :
    (c.ofIsPullback hsq).i ≫ pullback.snd c.g t = u :=
  pullback.lift_snd _ _ _

/-- The scheme of `c.ofIsPullback hsq` is noetherian as soon as the fibre product `c.Z ×_T S`
is: the two are the same scheme. -/
instance noetherianSpace_ofIsPullback_Z (hsq : IsPullback h u p t) (c : Compactification p)
    [hZ : TopologicalSpace.NoetherianSpace ↥(pullback c.g t)] :
    TopologicalSpace.NoetherianSpace (c.ofIsPullback hsq).Z :=
  hZ

/-- **The proper morphism of a base-changed compactification is a base change of the original
proper morphism**, for the compactification `c.ofIsPullback hsq`:

```
  c.Z ×_T S --------fst-------> c.Z
  |                              |
  (c.ofIsPullback hsq).g        c.g
  ↓                              ↓
  S ------------t-------------> T
```
-/
theorem isPullback_g_ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) :
    IsPullback (c.ofIsPullback hsq).g (pullback.fst c.g t) t c.g :=
  (IsPullback.of_hasPullback c.g t).flip

/-- **Base change of a compactification** along a morphism `t : T ⟶ S` of bases: if `c` is a
compactification of `f : X ⟶ S`, then `c.Z ×_S T ⟶ T` together with `X ×_S T ⟶ c.Z ×_S T`
is a compactification of the base change `pullback.snd f t`.
(blueprint: `def:nagata-compactification-base-change`,
`lemma:nagata-compactification-base-change`) -/
noncomputable def baseChange {f : X ⟶ S} (c : Compactification f) (t : T ⟶ S) :
    Compactification (pullback.snd f t) :=
  ofIsPullback (.of_hasPullback f t) c

@[simp] lemma baseChange_Z {f : X ⟶ S} (c : Compactification f) (t : T ⟶ S) :
    (c.baseChange t).Z = pullback c.g t := rfl

@[simp] lemma baseChange_g {f : X ⟶ S} (c : Compactification f) (t : T ⟶ S) :
    (c.baseChange t).g = pullback.snd c.g t := rfl

@[reassoc (attr := simp)] lemma baseChange_i_fst {f : X ⟶ S} (c : Compactification f)
    (t : T ⟶ S) :
    (c.baseChange t).i ≫ pullback.fst c.g t = pullback.fst f t ≫ c.i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma baseChange_i_snd {f : X ⟶ S} (c : Compactification f)
    (t : T ⟶ S) :
    (c.baseChange t).i ≫ pullback.snd c.g t = pullback.snd f t :=
  pullback.lift_snd _ _ _

/-- **Flat base change preserves scheme-theoretic density of a compactification.**

If the open immersion `c.i` of a compactification of `p` is scheme-theoretically dominant
and quasi-compact, then so is the open immersion of the base changed compactification along
a flat morphism `t`.

Flatness is essential: along an arbitrary base change the pulled back open need not be
dense. -/
theorem isSchemeTheoreticallyDominant_i_ofIsPullback (hsq : IsPullback h u p t)
    (c : Compactification p) (hc : IsSchemeTheoreticallyDominant c.i) [QuasiCompact c.i]
    [Flat t] :
    IsSchemeTheoreticallyDominant (c.ofIsPullback hsq).i :=
  have := hc
  .of_isPullback (c.isPullback_i_ofIsPullback hsq)

/-- **Flat base change preserves scheme-theoretic density of a compactification**, stated for
the literal fibre product, i.e. for `Compactification.baseChange`. -/
theorem isSchemeTheoreticallyDominant_i_baseChange {f : X ⟶ S} (c : Compactification f)
    (t : T ⟶ S) (hc : IsSchemeTheoreticallyDominant c.i) [QuasiCompact c.i] [Flat t] :
    IsSchemeTheoreticallyDominant (c.baseChange t).i :=
  isSchemeTheoreticallyDominant_i_ofIsPullback _ c hc

/-- If the proper morphism of a compactification of `p` is locally of finite presentation,
then so is the proper morphism of the base changed compactification. No flatness is needed:
finite presentation is stable under arbitrary base change. -/
theorem locallyOfFinitePresentation_g_ofIsPullback (hsq : IsPullback h u p t)
    (c : Compactification p) [LocallyOfFinitePresentation c.g] :
    LocallyOfFinitePresentation (c.ofIsPullback hsq).g :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd c.g t))

end Compactification

/-- **Compactifiability is stable under base change**: if `p : Y ⟶ T` admits a
compactification and `IsPullback h u p t`, then the base change `u : X ⟶ S` of `p` along
`t` admits one too.
(blueprint: `lemma:nagata-compactification-base-change`) -/
theorem HasCompactification.of_isPullback (hsq : IsPullback h u p t) [HasCompactification p] :
    HasCompactification u :=
  (Compactification.ofIsPullback hsq (HasCompactification.compactification p)).hasCompactification

/-- The second projection of a fibre product is a base change of the first leg of the
cospan, so it inherits compactifiability. -/
instance HasCompactification.pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasCompactification f] : HasCompactification (pullback.snd f g) :=
  .of_isPullback (IsPullback.of_hasPullback f g)

/-- The first projection of a fibre product is a base change of the second leg of the
cospan, so it inherits compactifiability. -/
instance HasCompactification.pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasCompactification g] : HasCompactification (pullback.fst f g) :=
  .of_isPullback (IsPullback.of_hasPullback f g).flip

end AlgebraicGeometry
