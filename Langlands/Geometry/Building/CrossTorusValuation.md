# Root-datum valuations under actual cross-torus isomorphisms

Author: Worker 118.

This internal construction extends `CrossTorusFunctions`. Over an arbitrary
field, let `e : S ≅ S'` and `f : G ≅ H` be actual commutative-group and ambient
group-scheme isomorphisms. Supply embeddings `i` and `j` whose square commutes,
monomorphism instances for both inclusions, and affine structural morphisms
for both ambient groups. No splitness, reductivity or local-field assumption
is imposed on this transport construction.

`rootDatumValuationTransportEquiv e f h` identifies the subtypes of full
`IsRootDatumValuation` families for `i` and `j`. Its underlying family is exactly
the existing `RootFunctionFamily.transportEquiv e f`. It adds no normalization
or rescaling of values. The same construction preserves and reflects
`IsSplitTorusCompatible` for the unchanged function `ω : kˣ → ℝ`; this latter
comparison does not require either monomorphism assumption.

The proof first identifies the images of the entire rational root groups and
filtration sets under the actual ambient point isomorphism. The unchanged-value
identity transports normalization, V0's cardinality bound, all three V1 subgroup
conditions and the value-at-infinity criterion. The actual character and
cocharacter action identities identify `RealizesReflection`; this transports
V2 with its original constant and conjugation orientation. For V3, the real
character map preserves the exclusion of the negative ray. Mapping the
commutator inclusion through the actual ambient homomorphism commutes with
subgroup commutators and generated subgroups. Each generator maps into the
target filtration indexed by the same positive integers, at the same level
`p*r + q*s`, using additivity of the character map and actual root transport.
V4 follows from preservation of twice a character, and V5 from actual
normalizer membership transport, multiplication and inversion. Applying
the forward result to the inverse square gives reflection of the entire
predicate and the stated subtype equivalence.

For split-torus compatibility the commuting square identifies the two actual
torus-point images. Character restriction and evaluation identify the evaluated
units under simultaneous torus-point and character transport. This proves
compatibility with exactly the original `ω`, without imposing any additional
property on that function. Applying the same argument to the inverse square
proves the reverse implication.

The provenance is internal: these are reindexing constructors and their
intrinsic laws, derived from the existing actual character, cocharacter,
root-group, normalizer and full-family transport interfaces. The named V0--V5
conditions and split-torus part of V6 refer to the already published
`RootDatumValuation` interface; no new external assertion or existence theorem
is introduced. Full centralizer V6 and V7, existence of apartment data,
transport of apartment points, apartment intersections, full A2 and general
building existence remain separate obligations.
