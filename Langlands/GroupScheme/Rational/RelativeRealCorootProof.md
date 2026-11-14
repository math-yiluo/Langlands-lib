# Real relative coroots

Worker 613, with Worker 656, Task 6346. Module
`Langlands.GroupScheme.Rational.RelativeRealCorootProof`, namespace
`Langlands.GroupScheme`.

`relativeRealCoroot.{u}` proves the exact published proposition
`RelativeRealCorootStatement.{u}`. It applies over every field to a connected
reductive group scheme, a maximal split torus, and every integral reflection
data `D : RelativeRootReflectionData i`. It proves all the clauses of that
proposition, including the possibly nonreduced full-root pairing and the reduced
indivisible-root pairing on the actual real root and coroot spans.

## Provenance and inputs

The source proposition formalizes Renard V.3.7, printed p.111 / PDF p.117 of
David Renard, *Représentations des groupes réductifs p-adiques*, French edition
of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The original-source
comparison and qualifications are in
[RelativeRealCorootStatements.md](RelativeRealCorootStatements.md). This proof
uses that published proposition without changing it or its imports. The helper
definitions and lemmas here are internal derived linear algebra implementing
its proof; they assert no additional original-source identification.

The main published inputs are `relativeRootSystem`,
`relativeCharacterRootComplement`, the invariant character-space form from
`RealTorusInvariantForm`, the perfect torus pairings from `RealTorusDuality`, and
the reflection and coroot-formula results in `LanglandsInvariantForm`. Mathlib
supplies finite-dimensional perfect-pairing criteria, `RootPairing.mk''`, and
finite crystallographic Cartan identities. Worker 656 contributed the generic
reducedness helper in
[IndivisibleRealRootReduced.md](IndivisibleRealRootReduced.md).

## Uniqueness and invariant forms

`RelativeRootReflectionData.realCoroot_unique` compares a vector satisfying the
invariant-form identity with the published identity for `D.realCoroot`. The
squared root length is strictly positive, so cancellation makes their pairings
against every character-space vector equal. Perfectness identifies the two
cocharacters. `coroot_eq_of_invariantForm` applies uniqueness to two reflection
data, tests their real coroots against integral characters, and uses the perfect
integral lattice pairing to identify their integral coroots.

`exists_relativeWeyl_realInnerProducts` uses the published Weyl average on
`Vstar T`. Its cocharacter counterpart averages a coordinate dot product over
the finite actual relative Weyl group. The identity summand gives strict
positivity; right multiplication reindexes the finite sum and proves invariance.

## Perfect pairing and the coroot span

`D.realSpanPairing` restricts the actual `pair T` to `relativeRootSpanReal i`
and `D.realCorootSpan`. The proof first establishes separation on both sides.
A root-span vector annihilating all coroots is orthogonal to every root by the
coroot formula, hence to its span and itself, and is zero by positivity.
Every coroot annihilates the restrictions of rational group characters. If a
coroot-span vector annihilates the root span too, the published character/root
complement and the full perfect pairing make it zero. Finite dimensionality
therefore gives `realSpanPairing_isPerfPair`.

Surjectivity on the right matches any cocharacter's functional on the root
span with a coroot-span vector. If the original cocharacter annihilates the
restricted group characters, their difference annihilates both complementary
character-space summands, so it vanishes. This proves
`realCorootSpan_eq_annihilator`. The same matching construction decomposes any
cocharacter into a common root annihilator plus a coroot-span vector;
restricted perfectness proves their intersection is zero. This gives
`central_isCompl_realCorootSpan` and the target's central decomposition.

## Full and indivisible real root systems

`realRootVector`, `realRootEmbedding`, and `realCorootEmbedding` put the actual
roots and coroots in their spans. The perfect lattice pairing proves that real
scalar extension is injective on characters; published coroot-functional
injectivity gives injectivity of the coroot family. Integral normalizer
reflections preserve the root family, and its real span is the ambient root
space by definition. `realRootPairing` applies Mathlib `RootPairing.mk''` to
these embeddings and `D.realSpanPairing`. The integral lattice pairing supplies
the integral Cartan entries, proving crystallographicity and the root-system
property. `realRootPairing_reflection` is the published real reflection formula.
`real_coreflection` follows by testing against every character and using Weyl
invariance and perfectness of the full pairing, and identifies the coreflection
with the actual representative action on `V T`.

`exists_indivisible_eq_or_twice` shows that each relative root is indivisible
or twice an indivisible root: the published bound on natural root multiples
makes any divisor exactly two, and a further divisor would violate that bound.
Consequently the indivisible roots still span the full real root space. The
actual Weyl action preserves indivisibility by applying its inverse to any
proposed divisor. `indivisibleRealRootPairing` uses `RootPairing.mk''` again with
the same restricted pairing and the indivisible-root embeddings. It is a
crystallographic root system on the same root and coroot spaces.

`indivisibleRealRoot_ne_two_smul` descends an alleged equality of real roots
through injective scalar extension to a prohibited double in the character
lattice. The generic `RootPairing.isReduced_of_no_double` then proves
reducedness: dependence forces the integral Cartan product to be four;
the two entries equal to two or minus two give equal or opposite roots, and
the other possibilities give prohibited positive or negative doubles.
Negative doubles reduce to positive doubles using a self-reflection.

Finally `relativeRealCoroot` takes root and Weyl finiteness from the published
relative root system, takes the published real character/root complement,
chooses an invariant form, and assembles the clauses above. Root values,
coroot values, and the restriction of `pair T` in both constructed pairings are
definitional equalities. No assertion of reducedness is made for the full
relative root set, and no additional claim about Weyl generation is added.
