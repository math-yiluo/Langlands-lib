# Relative H2 vanishing for finite p-group Galois extensions from all norms

`Langlands.ClassFieldTheory.Local.FinitePGroupNormH2Vanishing.{u}` is a
Prop-valued statement definition. For every natural number `p` with
`[Fact p.Prime]` and all fields `K L : Type u` in one arbitrary common
universe `u`, equipped with `Algebra K L`, it states: if `L/K` is finite
Galois, `Gal(L/K)` is a `p`-group, and the determinant norm

\[
N_{L/E}: L^\times \longrightarrow E^\times
\]

is surjective for every `E : IntermediateField K L`, then
`Subsingleton (relativeCohomology K L 2)`. The declaration specifies this
implication; this module supplies no proof of it, and nothing here asserts
that the vanishing holds.

## Exact objects and quantifiers

The quantifiers range over every prime `p`, every universe `u` (not only
`Type 0`), every pair of fields `K L : Type u` with an arbitrary
`Algebra K L` structure satisfying `FiniteDimensional K L` and
`IsGalois K L`, and every intermediate field of that extension.

The group hypothesis is Mathlib's `IsPGroup p Gal(L/K)`, where `Gal(L/K)` is
Mathlib's notation for `L ≃ₐ[K] L`: every automorphism has order a power of
`p`. Since `Gal(L/K)` is finite, Mathlib's `IsPGroup.iff_card` makes this
equivalent to its cardinality being a power of `p`. That cardinality is
`[L : K]` by `IsGalois.card_aut_eq_finrank`. The trivial extension (`L = K`)
satisfies the hypothesis for every `p`. The primality instance only fixes
`p` as a prime; it adds no hypothesis on the fields.

The norm is the existing `Langlands.LocalClassField.normUnits E L`, defined
as `Units.map (Algebra.norm E)`. Each intermediate field carries its actual
subfield structure and its canonical inclusion into `L`; no alternative scalar
actions are quantified. The local `FiniteDimensional E L` instance is
`FiniteDimensional.right K E L`, obtained from the finite extension `L/K` and
its canonical scalar tower. It adds no hypothesis. The norm family includes
every intermediate field, among them the bottom (the image of `K`, whose norm
corresponds to `N_{L/K}`), the top (`L`), and the fixed field of every
subgroup of `Gal(L/K)`.

The conclusion uses the underlying carrier of the existing Mathlib ordinary
group cohomology module:

```lean
relativeCohomology K L 2 = groupCohomology (unitsRepresentation K L) 2
```

Here `unitsRepresentation K L` has underlying module `Additive Lˣ`, with the
actual Galois action and scalar ring `IntegerScalars.{u} = ULift.{u} ℤ`. The
universe lift changes the scalar presentation, not the field, its units, or
its automorphism group. The subsingleton assertion says that this actual
second cohomology group vanishes.

The field, algebra, finite-dimensionality, Galois, `p`-group and displayed
norm-family assumptions are the entire antecedent. There is no H1 or H2
vanishing, cyclicity, comparison, local-field or reciprocity hypothesis.

## Relation to the general finite statement

The published `Langlands.ClassFieldTheory.Local.FiniteNormH2Vanishing.{u, v}`
in `Langlands/ClassFieldTheory/Local/FiniteNormH2Statement` has the same
norm family and conclusion, for arbitrary finite Galois `L/K` with `K` and `L`
in independent universes. Instantiating its universes as `{u, u}` gives this
statement, since this one only adds the `p`-group hypothesis. That
general module is unchanged.

The intended use runs the other way. For a Sylow `p`-subgroup `H` of
`Gal(L/K)`, the fixed field `E = L^H` is an intermediate field of `L/K`, so
`E` and `L` lie in the universe of `L` even when `K` does not. The extension
`L/E` is finite Galois with group isomorphic to `H`, a `p`-group. Each
intermediate field of `L/E` is also an intermediate field of `L/K`, with the
same subfield of `L`. The single common universe is therefore enough for this
Sylow step. It also matches the universe of the single-universe tower
statement `FiniteRelativeH2InflationExactness` mentioned below. This explains
why the statement is formulated this way. It is not a proof of either
statement.

## Source and derived scope

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`; retained original:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`
(SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`).
The relevant locations are Chapter X, Section 7, Proposition 11, its proof
and the following Remark, printed pages 161–162 (PDF pages 167–168), and
Chapter IX, Section 5, Theorem 8, printed page 145 (PDF page 151).

Serre's Proposition 11 is a field-wide equivalence about Brauer groups of all
finite separable extensions of a field. This statement is a finite-extension
specialization of its proof, not the field-wide equivalence, and it involves
no Brauer group. The source derivation is as follows. Let `G = Gal(L/K)` and
let `H` be a subgroup. Surjectivity of the norm from `L` to the fixed field
`L^H`, a member of the quantified family, gives
`Ĥ^0(H, L^×) = 0`. Chapter X, Section 1, Proposition 2 (printed page 150,
PDF page 156; Serre notes it is often called Hilbert's Theorem 90), cited in
that proof, gives `H^1(H, L^×) = 0`. Theorem 8 of Chapter IX, condition i),
asks for two consecutive vanishing degrees on a Sylow `ℓ`-subgroup for every
prime `ℓ`. When `G` is a `p`-group, its Sylow `p`-subgroup is `G` itself and
the other Sylow subgroups are trivial. So `L^×` is cohomologically trivial,
and in particular `H^2(G, L^×) = 0`. That derivation uses only the norm to the
bottom field. The statement nevertheless assumes the whole family, as its
specification requires. This keeps it parallel to the general statement above
and suits the proof route below.

The Remark after Proposition 11 reduces the norm condition to cyclic
extensions of prime degree. It passes to the solvable case by dévissage and
then to the general case through the Sylow subgroups. This statement is the
`p`-group stage of that strategy. A nontrivial finite `p`-group has a normal
subgroup of index `p`. A later proof may induct along such subgroups,
using the published `Langlands.ClassFieldTheory.Local.cyclicH2NormEquiv`
(ordinary relative H2 of a cyclic extension as the norm quotient),
`Langlands.ClassFieldTheory.Local.finiteRelativeH2InflationExactness`
(degree-two inflation–restriction exactness in finite Galois towers), and
norm transitivity. For an intermediate field `E`, every intermediate field of
`L/E` is an intermediate field of `L/K` with the same subfield of `L`. So the
norm-family hypothesis for `L/K` yields the corresponding hypothesis for
`L/E`, as such an induction requires. This paragraph
describes a possible proof route only; this module proves nothing about it.

Worker 262 authored the Lean/Markdown pair for the statement and source
localization specified by Worker 68's prerequisite request. It reuses the
norm-family formulation of the general statement written by Worker 84 to
Worker 37's specification.
