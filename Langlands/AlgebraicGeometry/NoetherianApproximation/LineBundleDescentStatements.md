# Descent of line bundles and their isomorphisms to finitely generated subalgebras

This module defines two propositions in namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation`, for an arbitrary universe `u`. It proves
neither. Both are noetherian-approximation steps for line bundles on a scheme over an affine
base. A line bundle is a module sheaf `M : X.Modules` satisfying the Library predicate
`Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne M`. That predicate asks every point to
have an open neighbourhood `U` with `M.restrict U.ι` isomorphic to the structure sheaf of `U`.

## Common setting

Both propositions quantify over commutative rings `A₀` and `A` in `Type u`, an algebra
structure `[Algebra A₀ A]`, and a scheme `X₀` with a quasi-compact, quasi-separated morphism
`f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)`. They also quantify over a scheme `X` with morphisms
`a : X ⟶ X₀` and `f : X ⟶ Spec (CommRingCat.of A)` satisfying

```lean
IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
```

So `X` is a base change of `X₀` to `Spec A`, presented by any pullback square, not necessarily
Mathlib's chosen one. Finally, both take a finite set `s : Finset A`. Their conclusions provide a
finitely generated `A₀`-subalgebra `T` of `A` containing `s`:
`∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧ ...`. Module pullback is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback`.

## The two propositions

`LineBundleSubalgebraDescentStatement` (descent of a line bundle). Let `M : X.Modules` satisfy
`IsLocallyFreeRankOne M`. Then there are `T` as above and a module
`M₀` on Mathlib's chosen fibre product
`pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))`, the base change of `X₀` to
`Spec T`, such that:
- `IsLocallyFreeRankOne M₀` holds;
- for every morphism `c : X ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))` with
  `c ≫ pullback.fst _ _ = a` and
  `c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A))`, there is an
  isomorphism `(Scheme.Modules.pullback c).obj M₀ ≅ M`.

The morphism `c` satisfying these two equations is the canonical comparison map from `X` to
the base change over `Spec T`, and it is unique by the universal property of the fibre product.
The conclusion therefore says that `M` is, up to isomorphism, the pullback of `M₀` along the
transition from `Spec A` to `Spec T`.

`LineBundleIsoSubalgebraDescentStatement` (descent of an isomorphism). Let `M N : X₀.Modules`
both satisfy `IsLocallyFreeRankOne`. Suppose
`Nonempty ((Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N)`, so the two
bundles become isomorphic on `X`. Then there is `T` as above with the following property. For
every scheme `X'` and morphisms `a' : X' ⟶ X₀` and `f' : X' ⟶ Spec (CommRingCat.of ↥T)` with
`IsPullback a' f' f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))`, there is an isomorphism
`(Scheme.Modules.pullback a').obj M ≅ (Scheme.Modules.pullback a').obj N`. So the two bundles
are already isomorphic on every base change of `X₀` to `Spec T`.

Neither proposition asserts any compatibility of the isomorphisms it provides. They only assert
that isomorphisms exist.

## Sources and provenance

Stacks Project, Chapter 32 *Limits of Schemes*, `limits.tex` at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` (registered as `stacks-limits-of-schemes-a04446e5`;
tags from its `tags-limits.txt`):

- Lemma 32.10.3 (tag 0B8W, label `lemma-descend-invertible-modules`, line 2608), part (2): for a
  limit `S = lim S_i` of quasi-compact, quasi-separated schemes with affine transition maps,
  every invertible `𝒪_S`-module is the pullback of an invertible `𝒪_{S_i}`-module for some
  `i`.
- Lemma 32.10.2 (tag 01ZR, label `lemma-descend-modules-finite-presentation`, line 2548), parts
  (2) and (3): morphisms between pullbacks of finitely presented modules descend to some later
  stage, and so do equalities of such morphisms. Applied to an isomorphism and its inverse, an
  isomorphism of the pullbacks of finitely presented modules descends to an isomorphism at
  some stage.

The limit is `X = lim X_T`, where `X_T` is the base change of `X₀` to `Spec T` and `T` runs over
the directed set of finitely generated `A₀`-subalgebras of `A` containing `s`. Each `X_T` is
quasi-compact and quasi-separated, being quasi-compact and quasi-separated over the affine
scheme `Spec T`, and the transition maps are affine. The two lemmas are stated for invertible
modules in the sense of the Stacks Project. Those agree with modules that are locally
isomorphic to the structure sheaf, which is what `IsLocallyFreeRankOne` expresses. Locally free
rank-one modules are finitely presented, so Lemma 32.10.2 applies to them. The formulation
with an arbitrary pullback square on the `A` side, and on the `T` side in the second
proposition, is derived. It is equivalent to the chosen-pullback formulation, because module
pullback along an isomorphism of squares preserves both rank one and isomorphism.

Implementation lead, not a proof source: the Anthropic FLT Lean source at revision
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered as
`anthropic-flt-complete-lean-source-6e837e75`, Apache-2.0) proves the analogous direct-limit
theorems
`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`
and
`AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`
(statements in `Theorems/Thm_*.lean` files of the same names). They use FLT's own invertibility
predicate `Scheme.Modules.IsInvertible` and an arbitrary directed system with `IsDirectLimit`.
The propositions here specialise them to the system of finitely generated subalgebras and use
the Library's `IsLocallyFreeRankOne`.
