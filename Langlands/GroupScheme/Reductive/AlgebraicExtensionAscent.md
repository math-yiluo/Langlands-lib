# Algebraic-extension ascent of connected reductivity and semisimplicity

The closing theorem `Langlands.GroupScheme.algebraicExtensionAscent.{u}`
proves exactly the published proposition
`Langlands.GroupScheme.AlgebraicExtensionAscentStatement.{u}` from
`Langlands.GroupScheme.Reductive.AlgebraicExtensionAscentStatement`.
The statement and its imported predicates are used unchanged.

For arbitrary fields `k K : Type u` with `Algebra k K` and
`Algebra.IsAlgebraic k K`, write

```lean
b = Spec.map (CommRingCat.ofHom (algebraMap k K))
G_K = (GroupScheme.baseChange b).obj G
```

for an actual group scheme `G` over `Spec k`. The module proves
`IsConnectedReductive G → IsConnectedReductive G_K` and
`IsSemisimple G → IsSemisimple G_K`. It imposes no further hypotheses.
The universe `u` is arbitrary, and algebraic extensions may be infinite or
inseparable, over imperfect fields of positive characteristic.

## Comparison of the geometric radicals

`IsConnectedReductive.geometricRadical_baseChange_of_algebraicExtension`
starts with the geometric radical condition for `G` over
`AlgebraicClosure k`. Since `K/k` is algebraic, Mathlib supplies
`IsAlgClosure k (AlgebraicClosure K)`. Thus

```lean
e := IsAlgClosure.equiv k (AlgebraicClosure K) (AlgebraicClosure k)
```

is a `k`-algebra equivalence. The inverse ring map gives
`d : Spec (AlgebraicClosure K) ⟶ Spec (AlgebraicClosure k)`.
The proof transports the original radical condition along this map using
`HasTrivialUnipotentRadical.baseChange_of_bijective` from
`Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange`, with the
bijectivity of `e.symm`.

Set `r = Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K)))`.
The scalar tower law proves `toAlgebraicClosure K ≫ b = r`, and the
`commutes` law of `e.symm` proves `d ≫ toAlgebraicClosure k = r`.
Two uses of `Descent.pullbackComparison` identify the resulting actual
pullback first with `(GroupScheme.baseChange r).obj G`, and then with
`(GroupScheme.baseChange (toAlgebraicClosure K)).obj G_K`.
`HasTrivialUnipotentRadical.of_iso` transports the condition through these
isomorphisms. The radical condition retains equality with the bottom
subgroup functor on every test scheme.

## Connected reductivity and semisimplicity

`IsConnectedReductive.baseChange_of_algebraicExtension` installs the
smoothness, affineness and connectedness supplied by its hypothesis.
Smoothness and affineness of `G_K` follow from the pullback instances.
`connectedSpace_baseChange_of_smooth_affine` gives connectedness, and the
preceding lemma gives the geometric radical condition over the chosen
`AlgebraicClosure K`.

`IsSemisimple.baseChange_of_algebraicExtension` combines this result with
`HasFiniteCenter.baseChange` from
`Langlands.GroupScheme.Reductive.FiniteCenterBaseChange`. This pulls back
an actual finite representative of the full scheme-theoretic centre.
The centre and radical predicates still use all test schemes, including
nonreduced schemes; no smoothness assumption is placed on the centre.

Finally, `algebraicExtensionAscent` packages the two implications into the
conjunction in the published target. It proves no assertion about covers
or simple connectedness.

## Provenance

This is a derived proof assembled from the published actual group-scheme
interfaces and Mathlib's algebraic-closure comparison. The mathematical
source correspondence is documented in the unchanged target statement's
paired Markdown. The implemented route is the algebraic-closure
isomorphism route described above.

The three helper proofs adapt Worker 1347's algebraic-ascent prototype;
the closing exact-target theorem follows Worker 1398's supplied assembly.
Worker 1483 prepared this pair for independent proof review.
