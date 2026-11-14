# Reductive Kottwitz functoriality from its named inputs

This module reduces the functoriality and torus compatibility of Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023), Lemma 11.5.1 (printed p. 430 / PDF p. 461) to inputs that it
assumes explicitly. It does not prove those inputs, and it does not prove
`ReductiveKottwitzFunctorialityStatement` outright.

Provenance: internal. KP prove the lemma's functoriality in one sentence: it "follows from
Lemma 11.4.3", the domination of z-extensions along a morphism (printed pp. 428–429 /
PDF pp. 459–460). The declarations here spell that argument out for the selected maps of
`ReductiveMap` and `ReductiveMapStatement`. The torus compatibility is the torus case of KP's
cocenter construction in §11.5.

## A torus is its own cocenter

`Cocenter.isFppfQuotient_id_of_isTorus` and `Cocenter.ofTorus` show that an actual torus `T`
is its own cocenter, with the identity as quotient map. The identity is flat, surjective and
locally of finite presentation. Its kernel is trivial, and so is the derived subgroup of a
commutative separated group (`derivedSubgroup_eq_bot_of_isCommMonObj`).

## The local square

`ReductiveKottwitzNaturalAt F k H G hH hG f` is the commuting square for one actual morphism
`f : H ⟶ G` of connected reductive groups. For every `K`-point `x` of `H`, where
`K = UnramifiedClosure F`, the reductive Kottwitz map of `G` at `f(x)` equals the induced
fundamental inertia map of `f` applied to the reductive Kottwitz map of `H` at `x`. It is the
first conjunct of `ReductiveKottwitzFunctorialityStatement` for that one morphism.

## Torus compatibility

`reductiveKottwitz_torus_of_inputs` assumes `FundamentalInertiaMapStatement`,
`SimplyConnectedDerivedKottwitzStatement` and `ReductiveKottwitzExistenceStatement`. A torus
has the trivial group as simply connected derived subgroup, so by the existence statement its
reductive map equals its simply-connected-derived map. The cocenter square of the latter for
`Cocenter.ofTorus` is the claimed identity. The identity morphism induces the identity on
inertia targets (by the identity law of `FundamentalInertiaMapStatement`) and on points.

## Naturality

`reductiveKottwitzNaturalAt_of_inputs` additionally assumes the two algebraic fundamental-group
statements `AlgebraicFundamentalGroupComparisonStatement` and
`AlgebraicFundamentalGroupMapStatement`, and `TorusInertiaComparisonStatement`. It also takes
two hypotheses written out in full, at the fixed fields:

- `hdom`, z-extension domination (KP Lemma 11.4.3): for connected reductive `G`, `H`,
  z-extensions `z` of `G` and `t` of `H`, and `f : G ⟶ H`, there are a z-extension `w` of `G`
  and morphisms `r : w.H ⟶ z.H`, `s : w.H ⟶ t.H` with `r ≫ z.p = w.p` and
  `s ≫ t.p = w.p ≫ f`. This is the body of the statement `ZExtensionMorphismDominationStatement`,
  which is not yet in the Library.
- `htnat`, torus Kottwitz naturality: for every morphism `f : S ⟶ T` of tori, the torus
  Kottwitz map of `T` at `f(x)` equals `torusInertiaMap` of `f` applied to the torus Kottwitz
  map of `S` at `x`.

The proof chooses a z-extension `t` of `G` and one `z` of `H`, and refines `z` to a
z-extension `w` of `H` with `s ≫ t.p = w.p ≫ f`. It lifts the point along `w.p`, which is
surjective on `K`-points by the existence statement. The z-extension squares for `t` and `w`
reduce both sides to simply-connected-derived maps. The published
`simplyConnectedDerivedKottwitz_natural_of_torus_naturality` for `s`, fed with `htnat` at the
induced cocenter morphism, then gives the square. Finally the composition law of
`FundamentalInertiaMapStatement` is applied twice, once to `s ≫ t.p` and once to `w.p ≫ f`.

## Assembly

`reductiveKottwitzFunctoriality_of_inputs` assembles both parts into
`ReductiveKottwitzFunctorialityStatement`. `TorusFundamentalComparisonStatement` is supplied
by its published proof `torusFundamentalComparison_proof`. Here `hdom` is quantified over every
field `k`. `htnat` is quantified over every local field `F` and every compatible
coefficient-field tower, including the binder `[IsSepClosure k (SeparableClosure F)]` that the
target statement also carries. Because of that binder, `htnat` asks for torus naturality only
when the separable closure of `F` is a separable closure of `k`. A version without the binder
implies it.
