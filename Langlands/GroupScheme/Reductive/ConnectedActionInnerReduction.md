# Clopen subgroups over connected residue fibres

Worker 681. This is a derived supporting construction for Task 6418.
It proves the elementary connected-fibre part of the inner-action argument.
The unconditional inner-action theorem still requires a proof of
`ReductiveInnerActionLocusStatement`.

`clopen_eq_univ_of_section_connectedFibres` concerns a scheme morphism
`p : X → S`, a section `e`, connected scheme-theoretic residue fibres, and a
clopen subset `Z` of `X` containing the section. It proves `Z = X`. The proof
pulls `Z` back to each residue fibre. The section makes this clopen preimage
nonempty, so connectedness makes it the whole fibre. Every point of `X` lies
in the residue fibre of its image in `S`.

`isIso_clopen_subgroup_of_connectedFibres` applies this lemma to the range of
a homomorphism `j : K → H` whose underlying scheme map is both an open
immersion and a closed immersion. The unit section of `H` lies in this range
because `j` preserves units. If the residue fibres of `H` are connected, the
lemma makes `j` surjective. A surjective open immersion is an isomorphism of
schemes. The forgetful functors from group objects to monoid objects, to
schemes over `S`, and to schemes reflect isomorphisms, so `j` is an
isomorphism of group schemes.

`clopenSubgroupIsoOfConnectedFibres` packages this result as an actual
isomorphism `K ≅ H`, with forward homomorphism `j` and inverse `inv j`, using
`CategoryTheory.asIso`. The base scheme and group schemes are arbitrary in
universe `u`. There are no flatness, smoothness, affineness, finiteness or
nonempty-base hypotheses. Connectedness is required of the scheme-theoretic
fibres over every residue field of `S`, using the published group-scheme
base-change interface.

`reductiveConnectedActionInner_of_innerActionLocus` has the type

```text
ReductiveInnerActionLocusStatement.{u} →
ReductiveConnectedActionInnerStatement.{u}
```

It takes a proof of the published inner-action locus proposition, obtains
its `K`, `j` and `φ`, and applies the connected-fibre result to make `j` an
isomorphism. The required homomorphism is `inv j ≫ φ`. Functoriality of
restriction proves the required equality of actions. Applying the locus's
universal property to any other compatible homomorphism from `H` gives a
map to `K` whose composite with `j` is the identity. That map is `inv j`,
which proves uniqueness. The action-restriction calculations use the published
`AutomorphicAction.restrict_id` and `AutomorphicAction.restrict_restrict`
lemmas through `Rational.RootFactorPairExistenceReduction`.

## Provenance and remaining obligation

This construction uses the existing Mathlib fibre, connectedness and
open-immersion APIs and the published group-scheme and action interfaces.
The fibre argument is elementary: a nonempty clopen subset of a connected
space is the entire space, and an open immersion that is surjective is an
isomorphism. The categorical argument uses the universal property explicitly
supplied by the inner-locus premise. No external mathematical result is
assumed beyond these imported interfaces.

The published statement
[`ReductiveInnerActionLocusStatement`](InnerActionLocusStatement.md) describes
the source-derived clopen locus and its universal property. Its proof is the
separate prerequisite Task 7304 (`bb1c1b2f-f10a-4a67-9d4e-a2ec97df6574`).
The conditional reduction in this module is a supporting theorem; it does
not assert or prove that premise. The designated construction and this
reduction therefore do not establish the unconditional proposition
`ReductiveConnectedActionInnerStatement` required by Task 6418.

