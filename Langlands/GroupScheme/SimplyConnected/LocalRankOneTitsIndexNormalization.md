# Small Cartan diagrams in the local rank-one index enumeration

Author: Worker 177.

This is an internal derivation from the published actual `TitsIndexData` and
`LocalRankOneTitsIndexStatement` interfaces and Mathlib's integral Cartan matrices.
It proves finite diagram and full-star consequences, over an arbitrary field
`K : Type u`. It makes no local-field admissibility assertion.

`starPermutation` packages the actual action of each full absolute Galois
element as a permutation of the actual simple vertices. Its inverse is the
action of the inverse Galois element; the two inverse identities follow from
`star_mul` and `star_one`. `numberedStar` transports that permutation along a
supplied numbering `e`, so its value at `i` is exactly
`e (d.star σ (e.symm i))`, as recorded by `numberedStar_apply`.

`cartan_star` follows from the pairing identity of the based-root-datum
automorphism defining each full absolute Galois element's star action.
`IsNumberingOf.relabel` composes an actual numbering with a bijection of the
numbering sets. It requires equality of every old and new Cartan entry and an
iff between the two marked predicates, and preserves both exactly.

`star_cases_of_cartan` uses `numberedStar` for each Galois element.
The resulting permutation preserves the numbered Cartan matrix. An explicit
classification of all matrix-preserving functions therefore bounds that entire
Galois element by the displayed permutations. The choice of permutation is
outside the vertex quantifier. `starIsTrivial_of_cartan_rigid` applies this to a
rigid matrix. `starImagePair_of_cartan_symmetry` additionally uses nontriviality
of the actual full action: an element moving one vertex cannot be the identity
case and hence realizes the nonidentity permutation on every vertex.

The closed finite Cartan calculations use kernel-checked `decide`, without
native evaluation. For A2 and A3, every matrix-preserving function is identity
or chain reversal, and reversal is nonidentity. Consequently a nontrivial
full star action has exactly the pair image required by `StarImagePair`.
For C2 and C3 the only matrix-preserving function is identity, so the full
star action is automatically trivial. These are integral Cartan calculations;
no restriction on the field or residue characteristic is introduced.

The remaining lemmas implement the small-rank coincidences needed when
normalizing an eventual admissibility enumeration:

- Any numbering by `Fin 1` forces the full action to be trivial. A fully
  distinguished A1, B1 or C1 diagram gives `HasRankOneInnerAIndex 1`.
- Swapping B2's zero-based vertices 0 and 1 identifies every Cartan entry with
  C2 and takes the distinguished vertex 0 to 1. This gives
  `HasRankOneCIndex 2`; its trivial full action follows from C2 rigidity.
- Swapping D3's vertices 0 and 1 identifies every Cartan entry with A3. A
  distinguished D3 central vertex 0 becomes A3's middle vertex 1. Together
  with the supplied trivial full action this gives
  `HasRankOneInnerAIndex 2`.
- Under the same swap, the two distinguished D3 tips 1 and 2 become A3's
  endpoints 0 and 2. A supplied nontrivial full action then gives
  `HasRankOneOuterAIndex 3` by the A3 symmetry calculation. Its precise
  two-element image is proved, rather than assumed.

The field group retains the affine and locally finite type instances required
by `TitsIndexData`. Every numbering and distinguished subset is actual, and
the star statements quantify over `SeparableClosure K ≃ₐ[K] SeparableClosure K`.
These lemmas do not prove the existence of a numbering, marked subset or
nontrivial action for any local group. In particular the exceptional and
trialitarian exclusions and the unconditional enumeration remain open.
