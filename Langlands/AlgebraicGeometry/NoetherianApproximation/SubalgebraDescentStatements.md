# Descent of schemes and morphism properties to finitely generated subalgebras

This module defines five propositions in namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation`, for an arbitrary universe `u`. It proves
none of them. They are the noetherian-approximation steps for a scheme over an affine base.
The base ring `A` is the directed union of its finitely generated `A₀`-subalgebras. Each
proposition says that a scheme, or a property of a morphism, over `Spec A` already comes from
`Spec T` for one such subalgebra `T`.

## Common shape

Every proposition quantifies over commutative rings `A₀` and `A` in `Type u` and an algebra
structure `[Algebra A₀ A]`. Its conclusion has the form

```lean
∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧ ...
```

for a given `s : Finset A`. So `T` is a finitely generated `A₀`-subalgebra of `A` that contains
the finite set `s`. The finite set lets several descents be combined: one forces the next `T` to
contain the generators of an earlier one. Rings are viewed as schemes through
`Spec (CommRingCat.of A₀)`, `Spec (CommRingCat.of A)` and `Spec (CommRingCat.of ↥T)`. Base change
uses the maps `Spec.map (CommRingCat.ofHom (algebraMap A₀ A))`,
`Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))` and
`Spec.map (CommRingCat.ofHom (algebraMap ↥T A))`. `pullback` and `pullback.snd` are Mathlib's
chosen fibre product and its second projection. All morphism properties are Mathlib's:
`QuasiCompact`, `QuasiSeparated`, `LocallyOfFinitePresentation`, `LocallyOfFiniteType`,
`IsSeparated`, `Smooth`, `IsProper` and `GeometricallyConnected`. The hypotheses are instance
binders inside the quantifier.

## The five propositions

`SchemeSubalgebraDescentStatement` (descent of a scheme). Let `g : X ⟶ Spec A` be quasi-compact,
quasi-separated and locally of finite presentation, and let `s : Finset A`. Then there are `T` as
above, a scheme `X₀`, a morphism `f₀ : X₀ ⟶ Spec T` and a morphism `π : X ⟶ X₀` such that:
- `f₀` is locally of finite presentation, quasi-compact and quasi-separated;
- `IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))` holds.

So `X` is the base change of `X₀` along `Spec A ⟶ Spec T`, through an actual pullback square,
not only an abstract isomorphism.

`SmoothSubalgebraDescentStatement` (descent of smoothness). Let `f : X ⟶ Spec A₀` be quasi-compact
and locally of finite presentation. Suppose the base change
`pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))` is `Smooth`. Then for every
`s` there is `T` as above with
`Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))`.

`IsSeparatedSubalgebraDescentStatement` (descent of separatedness). The same with `f`
quasi-compact and quasi-separated, and `IsSeparated` in place of `Smooth`.

`IsProperSubalgebraDescentStatement` (descent of properness). Here `A₀` is moreover a noetherian
ring, `[IsNoetherianRing A₀]`. Let `f : X ⟶ Spec A₀` be separated, quasi-compact and locally of
finite type, with proper base change to `Spec A`. Then the base change to some `Spec T` is
`IsProper`.

`GeometricallyConnectedSubalgebraDescentStatement` (descent of geometric connectedness). Here too
`A₀` is noetherian. Let `f : X ⟶ Spec A₀` be proper and smooth. Suppose its base change to
`Spec A` is `GeometricallyConnected`, which means all its fibres over field points are
geometrically connected. Then the base change to some `Spec T` is `GeometricallyConnected`.

The noetherian hypotheses on `A₀` in the last two propositions only narrow their scope. They
match the implementation lead below. In the intended use, `A₀` is a finitely generated
`ℤ`-algebra.

## Sources and provenance

Stacks Project, Chapter 32 *Limits of Schemes*, `limits.tex` at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` (registered as `stacks-limits-of-schemes-a04446e5`;
tags from its `tags-limits.txt`):

- Lemma 32.10.1 (tag 01ZM, label `lemma-descend-finite-presentation`, line 2370), part (1):
  for a limit `S = lim S_i` of quasi-compact, quasi-separated schemes with affine transition
  maps, every scheme of finite presentation over `S` is the base change of one of finite
  presentation over some `S_i`.
- Situation 32.8.1 (tag 081D, label `situation-descent-property`, line 1739), the setting of
  Section 32.8 *Descending properties of morphisms* (tag 081C).
- Lemma 32.8.6 (tag 01ZQ, label `lemma-descend-separated-finite-presentation`, line 1851):
  separatedness of `f` descends to some `f_i`.
- Lemma 32.8.9 (tag 0C0C, label `lemma-descend-smooth`, line 1931): smoothness descends when
  `f₀` is locally of finite presentation.
- Lemma 32.13.1 (tag 081F, label `lemma-eventually-proper`, line 3265): properness descends when
  `f₀` is locally of finite type.
- Lemma 32.4.10 (tag 05F4, label `lemma-limit-contained-in-constructible`, line 530): if the
  limit maps into a locally constructible subset of a stage, so do all later stages.

Here `S = Spec A` is the limit of `S_T = Spec T` over the directed set of finitely generated
`A₀`-subalgebras `T` of `A`. Each `S_T` is affine, hence quasi-compact and quasi-separated, and
the transition maps are affine. The subalgebras containing `s` are cofinal. Situation 32.8.1 is
applied with `S_0 = Spec A₀`, `Y_0 = S_0` and `X_0 = X`. It asks `X_0` to be quasi-compact and
quasi-separated. In the separatedness proposition this is the hypothesis on `f`. In the
properness proposition `f` is separated, hence quasi-separated, and quasi-compact. The smoothness
proposition assumes only that `f` is quasi-compact. This still suffices: smoothness is local on
the source, so one covers `X` by finitely many affine opens, each of finite presentation over
`Spec A₀`, and applies the lemma to each of them.

Geometric connectedness has no single lemma in that chapter. Its proposition is derived as
follows. Let `f` be proper and smooth, hence flat, of finite presentation and with reduced
geometric fibres. By Stacks Project *More on Morphisms*, Lemma `lemma-proper-flat-geom-red`
(tag 0E0N; `more-morphisms.tex` at the same commit, lines 15425–15436, registered as
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`), the number of geometric connected
components of the fibres of `f` is locally constant on `Spec A₀`. Hence the set `E` of points
of `Spec A₀` with geometrically connected fibre is open and closed, in particular constructible.
The image of `Spec A` lies in `E`, because the fibres of the base change to `Spec A` are base
changes of fibres of `f`. Lemma 32.4.10 then puts the image of some `Spec T` in `E`.

Implementation lead, not a proof source: the Anthropic FLT Lean source at revision
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered as
`anthropic-flt-complete-lean-source-6e837e75`, Apache-2.0) proves theorems of exactly these
forms, in universe `u`, on its own Lean/Mathlib pin:
`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`,
`AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd`,
`AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd`,
`AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd` and
`AlgebraicGeometry.GeometricallyConnected.exists_fg_subalgebra_of_geometricallyConnected_pullback_snd`
(statements in `Theorems/Thm_*.lean` files of the same names, proofs under `P2M/Sol/`). The five
propositions here are their statements, written as `Prop`-valued definitions with Mathlib
notions only.

## Licence and attribution

The Lean text of the five proposition bodies is copied from the statements of the five FLT
theorems named above, in the files
`Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.lean`,
`Theorems/Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.lean`,
`Theorems/Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.lean`,
`Theorems/Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.lean` and
`Theorems/Thm_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`. That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. The binders, hypotheses and conclusions are kept
unchanged. The adaptation makes only these changes:

- each `theorem` declaration becomes a `Prop`-valued `def` whose binders, including the instance
  binders, are universally quantified;
- the declarations are renamed and moved from the namespaces `AlgebraicGeometry`,
  `AlgebraicGeometry.Smooth`, `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.IsProper` and
  `AlgebraicGeometry.GeometricallyConnected` to
  `Langlands.AlgebraicGeometry.NoetherianApproximation`;
- the FLT imports are replaced by Mathlib imports, and the proof terms are omitted.

The Lean file carries a notice recording this adaptation. Unmodified copies of the source's
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` accompany this contribution as
`licenses/Anthropic-FLT/LICENSE`, `licenses/Anthropic-FLT/NOTICE` and
`licenses/Anthropic-FLT/ATTRIBUTION.md`. The source's `NOTICE` begins:

> Fermat's Last Theorem in Lean 4
> Copyright 2026 Anthropic, PBC
>
> This repository is made available under the Apache License, Version 2.0 (see the file LICENSE).

`ATTRIBUTION.md` lists, file by file, the FLT files that contain third-party material. It has no
row for any of the five theorem files above, so no third-party notice is recorded for them. Its
section 5, "What we are not certain of", states the limits of that file-by-file check, and those
limits apply here as well.
