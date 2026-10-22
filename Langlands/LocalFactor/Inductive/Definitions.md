# Inductive functions of Weil representations: definitions

Worker 33 wrote this definition module for task `e534647a` (row 10 of the
local-factor coverage map). It defines the objects of Tate's §2.3 for p-adic
fields: representations of Weil groups of finite extensions, induction along a
tower, and Tate's additive, inductive and degree-zero-inductive functions
(Tate 1979, (2.3.2)). Every group, representation, virtual group and induction
used here is an existing Library construction. This module adds no new
mathematical structure. It packages those objects under Tate's names and proves
the compatibility lemmas for their use in this interface.

## Finite extensions and their Weil groups

Fix a prime `p`. A p-adic field is the Library's `PadicField p`: a field that is
a finite-dimensional algebra over `ℚ_p`. Its local Weil group `W_E` is the
Library's `Weil.Local.localWeilGroup E`, built in `Langlands.Weil.Local.Assembly`
(Workers 9, 28 and 53).

`Extension F` is a structure with two fields:

- `field : PadicField p`, a p-adic field `E` in the universe of `F`;
- `embedding : F.Carrier →ₐ[ℚ_p] E.Carrier`, an embedding of `F`.

This is the abstract form of a finite extension `E/F`. The Library's
`Langlands.Weil.Local.ExtensionParameters` uses the same form. For extensions `E`
and `E'` of `F`, an embedding `g : E → E'` over `ℚ_p` is a tower `E'/E/F` when
`g ∘ embedding_E = embedding_{E'}`. This condition is `IsTower E E' g`.

For an embedding `g : E → E'`, Worker 53's `extensionWeilMap E E' g : W_{E'} → W_E`
is the actual map of local Weil groups. It is a continuous injective
homomorphism and an open embedding (`extensionWeilMap_isOpenEmbedding`). Its
range is an open subgroup of index `[E' : E]` (`extensionWeilMap_range_index`,
with the shared instance `extensionWeilRange_finiteIndex`). In Tate (1.1), `W_{E'}`
is the preimage in `W_E` of the Galois group of `E'`, which is an open subgroup of
finite index. Tate notes on p.4 that this subgroup is a Weil group for `E'`. Here
`W_{E'}` is the Library's own Weil group of `E'`, identified with that open subgroup
through the Weil map. Tate's unicity theorem (1.3.1) says the two descriptions
agree up to isomorphism.

## Representations and virtual representations

Tate's §2 opening defines a representation of a topological group `G` as a
continuous homomorphism `G → GL(V)`, with `V` a finite-dimensional complex vector
space. The module uses these objects:

- `IsRepresentation E A` is the Library's usual-topology continuity predicate
  `FiniteRepresentation.IsContinuous` (Worker 17). Here `A` is a
  finite-dimensional complex representation of `W_E` whose carrier lies in the
  universe of `E`.
- `Classes E` is Tate's `M(W_E)`: the Library's isomorphism classes of such
  representations (`IsomorphismClassesWith`).
- `Virtual E` is Tate's `R(W_E)`: Workers 20 and 24's exact-relation virtual group
  `ExactGrothendieckGroup`. It is the free abelian group on `M(W_E)` modulo
  `[V] = [V'] + [V'']` for every actual short exact sequence. These are the
  relations Tate imposes when he extends an additive function to `R`.
- `VirtualDegreeZero E` is Tate's `R⁰(W_E)`, the kernel of the virtual degree.
- `virtualClass E` is the class map `V ↦ [V]`.
- `characterClass E χ` is the class of the one-dimensional representation of a
  quasi-character `χ : W_E → ℂ^×`, which is a continuous homomorphism. It uses
  Worker 20's `continuousCharacterLine`, where `W_E` acts on a lifted copy of `ℂ`
  by the scalar `χ(w)`. Tate identifies one-dimensional representations with
  quasi-characters through `det` (§2 opening).
- `trivialClass E` is `[1_E]`, the class of the trivial character.
- `rank_characterClass` records that these classes have dimension one.

## Induction

`induceClass E E' g : M(W_{E'}) → M(W_E)` is induction along the Weil map. It is
Worker 17's `continuousInduceAlongClass` for the open embedding
`extensionWeilMap E E' g`. Worker 17's `induceAlong` restricts along the inverse
of the Weil map on its range, then induces from that finite-index range by the
Library's equivariant-function construction. Continuity of the result is
Worker 17's `isContinuous_induceAlong`.

`virtualInduce E E' g : R(W_{E'}) → R(W_E)` is Tate's `Ind_{E'/E}`. It is the
homomorphism induced by `induceClass` through the universal property `lift` of the
exact virtual group. Its well-definedness needs induction to preserve short exact
sequences. That is Worker 20's `isShortExact_induce`, combined with the published
`FiniteRepresentation.isShortExact_restrict_iff` from
`Langlands.VirtualRepresentation.ExactRestriction`: restriction keeps the same
linear maps, so exactness is unchanged. Its `FiniteRepresentation.restrictMap`
is the same intertwiner viewed between restricted representations. This module
reuses those general declarations.

The module also proves:

- `virtualInduce_virtualClass` and `virtualInduce_ofRepresentation`: on the class
  of a representation, `virtualInduce` is the class of the induced representation.
- `degree_virtualInduce`: induction multiplies the virtual degree by `[E' : E]`.
  This follows from Worker 17's `rank_induceAlong` and Worker 53's index theorem.
  In particular `Ind_{E'/E}` maps `R⁰(W_{E'})` into `R⁰(W_E)`.

## Tate's inductive functions

Tate (2.3.2) considers a function `λ` that assigns to each finite extension
`E/F` and each `V ∈ M(W_E)` an element `λ(V)` of an abelian group `X`.

- `ClassFunction F X` is the type of such `λ`, indexed by `E : Extension F`.
  Tate writes `X` multiplicatively; the Lean target is an additive commutative
  group. A multiplicative target such as `ℂ^×` is used as `Additive ℂ^×`.
- `IsAdditive F X λ`: for every `E`, `λ_E` is additive on every actual short exact
  sequence of representations of `W_E` (Library predicate `IsExactAdditive`).
- `virtualExtension F X λ hλ E : R(W_E) → X` is the extension of an additive `λ_E`
  to a homomorphism, as in Tate (2.3.2).
- `IsInductive F X λ`: `λ` is additive and `λ_E ∘ Ind_{E'/E} = λ_{E'}` on `R(W_{E'})`
  for every tower `E'/E/F`. This is Tate's commutative diagram on p.12.
- `IsInductiveInDegreeZero F X λ`: `λ` is additive and the same identity holds on
  `R⁰(W_{E'})` for every tower.

Tate writes a tower as `E/E'/F` with `E` the larger field. Here `E` is the smaller
field and `E'` the larger, so Tate's `Ind_{E/E'}` is `virtualInduce E E' g`.

## Scope and conventions

- Only p-adic fields are covered. Tate's §2.3 also covers archimedean,
  equal-characteristic and global fields; those are outside this module.
- Tate takes finite separable extensions of `F` inside a fixed separable closure.
  Here an extension is any p-adic field with an embedding of `F`. Extensions
  inside a closure correspond to these up to isomorphism, and every finite
  extension of a p-adic field is separable.
- Carriers of representations lie in the universe of the fields. Every
  finite-dimensional complex representation has an isomorphic copy there, so
  this only fixes the bookkeeping. Induction along the Weil map keeps carriers in
  that universe.
- No continuity, unitarity or semisimplicity condition is added beyond Tate's
  continuity.

## Provenance

The definitions transcribe Tate's §2 opening and (2.3.2). The realization of
`W_{E'}` and of induction uses the Library's actual Weil map instead of a
subgroup of a fixed `W_F`; the identification is explained above. The exactness
compatibility is an internal derivation from the published induction and
restriction lemmas.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: J. Tate,
  *Number theoretic background*, Corvallis Part II (1979). PDF page = printed
  page + 9.
  - §1 opening and (1.1), printed pp.3–4 (PDF pp.12–13): transfer, `W_E` as the
    preimage of `G_E`, and `W_E` as a Weil group for `E`.
  - (1.3.1), printed p.5 (PDF p.14): unicity of Weil groups.
  - §2 opening, printed p.9 (PDF p.18): representations, quasi-characters, `M(G)`.
  - (2.3) opening and (2.3.2), printed pp.11–12 (PDF pp.20–21): `[V]`, `R⁰`,
    additive, inductive and degree-zero-inductive functions.
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*
  (1973). §1.1, printed p.507 (PDF p.7), defines the virtual representation group
  as the Grothendieck group of finite-dimensional representations. It extends a
  function that is additive on exact sequences to a homomorphism, and defines the
  dimension, the determinant, and induction from a finite-index subgroup.

## Dependencies and status

Imports, all published in the Library:

- `Langlands.VirtualRepresentation.ExactInduction` (Worker 20);
- `Langlands.VirtualRepresentation.ExactRestriction`;
- `Langlands.Weil.Local.ExtensionWeilRange` (Worker 53);
- `Langlands.Weil.Representation.CharacterLine` (Worker 20);
- `Langlands.Weil.Representation.InductionContinuity` (Worker 17).

A development check in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed29652`) compiled the module with no errors or
warnings. The companion statement module
`Langlands.LocalFactor.Inductive.Statement` (Tate 2.3.1, 2.3.3, 2.3.4, Gallagher's
formula and the degree correction) is submitted separately after this module is
published.
