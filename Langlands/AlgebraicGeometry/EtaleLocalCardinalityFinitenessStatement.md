# Finiteness of separated etale morphisms from local fibre counts

## Statement and quantifiers

`Langlands.AlgebraicGeometry.EtaleLocalCardinalityFinitenessStatement.{u}`
is a Prop-valued definition, for every universe `u`. It asserts the following
implication for schemes `X`, `Y : Scheme.{u}` and `f : X ⟶ Y`.

Assume `QuasiCompact f`, `IsSeparated f` and `Etale f`. For every commutative
local ring `R : Type u` and every morphism
`b : Spec (CommRingCat.of R) ⟶ Y`, assume there is a natural number `n` such that
for every algebraically closed field `k : Type u`, with every `R`-algebra
structure, the set

```text
{x : Spec (CommRingCat.of k) ⟶ X //
  x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ b}
```

has `Nat.card` equal to `n`. Then `IsFinite f`.

The existential `n` follows `R`, its ring and local-ring structures, and `b`,
but precedes `k`, its field and algebraic-closure structures, and its
`R`-algebra structure. Thus one number works for all these field-valued tests
of a fixed local base. The subtype counts actual scheme morphisms lifting the
specified composite into `Y`. It does not refer to a supplied finite model.
The conclusion is the usual Mathlib finiteness property of the original
morphism. There is no noetherian hypothesis.

## Finite fibre meaning of the cardinality

The geometric assumptions already ensure that each counted type is finite,
without assuming that `f` itself is finite. After base change along the
specified morphism `Spec k ⟶ Y`, the resulting scheme is quasi-compact and
etale over `k`. An etale scheme over a field is locally a disjoint union of
spectra of finite separable field extensions; quasi-compactness makes this
union finite. Since `k` is algebraically closed, this is a finite disjoint
union of copies of `Spec k`. Its `k`-sections correspond, by the pullback
property, exactly to the displayed lifts.

Consequently `Nat.card` is the ordinary finite geometric fibre count here.
Although `Nat.card` on an infinite type is zero, that convention introduces
no extra case under these hypotheses. Zero is allowed and represents an
empty geometric fibre. The same count is the number of geometric connected
components of the fibre.

## Why the local-base hypothesis suffices

This paragraph gives the mathematical derivation motivating the statement;
the Lean file defines the proposition and does not prove it.

Write `d(y)` for the finite geometric fibre cardinality over `y ∈ Y`.
Etaleness gives local finite presentation, and separatedness gives
quasi-separatedness. Together with quasi-compactness, this makes `f` a
morphism of finite presentation. Stacks Lemma 37.28.6 (Tag 055I) says that
the level sets of the number of geometric connected components are locally
constructible for such a morphism. For these fibres, those are the level
sets of `d`.

Fix `y` and a generalization `z` of `y`. Apply the assumed local-base
condition to `R = O_{Y,y}` and the canonical `Spec R ⟶ Y`. Algebraic
closures of the residue fields at the closed point and at the prime
corresponding to `z` give two permitted `R`-algebra tests. Their lift counts
are `d(y)` and `d(z)`. Both equal the same `n`, so `d(y) = d(z)`.
These local rings and algebraic closures can be taken in `Type u`; the
statement does not require tests in a larger universe.

Thus each level set of `d` is stable under generalization. On every affine
open of `Y` it is constructible, by local constructibility and
quasi-compactness of the affine open. Stacks Lemma 10.41.7 (Tag 00I0) makes
each such level set open, with no noetherian assumption. Hence `d` is
locally constant.

The standard criterion for a quasi-compact separated etale morphism with
locally constant geometric fibre cardinality now gives finiteness.
Conrad uses precisely this criterion on p.96 in the proof of Proposition
3.2.8, referring to EGA IV4, 18.5.11(c). That EGA clause supplies the
finite open-and-closed pieces over a henselian local base. EGA IV4,
Remark 18.10.17, especially p.166, explicitly removes the noetherian
hypothesis for the separated quasi-finite finite-presentation criterion
and explains how constant geometric degree forces the remaining open
piece to be empty. Applied to an etale morphism, this supplies the
criterion over arbitrary bases.

## Provenance and sources

The universal local-base formulation is an internal derived variant,
chosen for applications where a constant finite root datum controls all
field-valued tests over a local ring. It is not a quotation of Conrad or
EGA. The source criterion concerns locally constant geometric degree; the
preceding derivation explains the additional sufficient condition.

- Brian Conrad, *Reductive group schemes* (2014), p.96, proof of
  Proposition 3.2.8. Registered source
  `conrad-2014-reductive-group-schemes`, SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
- A. Grothendieck and J. Dieudonne, *Elements de geometrie algebrique IV,
  Quatrieme partie* (1967), Theorem 18.5.11(c), p.131, and
  Remark 18.10.17, pp.165–166, especially the finiteness argument on p.166.
  Registered source `grothendieck-dieudonne-ega-iv4-1967`, SHA-256
  `b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
  The volume's List 3 errata was checked for these identifiers; no
  correction was found in that check.
- The Stacks Project Authors, Lemma 37.28.6
  ([Tag 055I](https://stacks.math.columbia.edu/tag/055I)) and
  Lemma 10.41.7 ([Tag 00I0](https://stacks.math.columbia.edu/tag/00I0)),
  retained as `055I.html` and `00I0.html` in registered source bundle
  `stacks-etale-local-cardinality-2026-11-14`, SHA-256
  `518d3a75363a0d9e6ec7c32b7a54c59c9baeb393d33636578387476058883bf3`.
  Both complete lemmas and proofs and the two comments on 055I were read.
  The retained 055I statement already uses geometric connected components.

Existing Library results about cardinality or rank of finite etale
morphisms already assume finiteness. This statement provides a separate
target for establishing finiteness from local fibre counts.
