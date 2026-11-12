# Even-chain Galois data for orthogonal simple-root orbits

Provenance: internal. This module proves the orthogonal-orbit case of the
existence conclusion in `EvenChainGaloisDataStatement` from the actual pinning,
Galois transport and orbit-block constructions already in the Library. It does
not establish the general case, which also permits nonorthogonal orbits.

For arbitrary fields `k,K : Type u` with an algebra structure, an affine group
scheme `G/k`, and `D : GaloisCompatiblePinningData k K G`, the theorem
`GaloisCompatiblePinningData.exists_evenChainGaloisData_of_orthogonal` assumes
`D.pinning.OrthogonalSimpleOrbits D.action` and constructs all the data required
by that conclusion. No finiteness or Galoisness hypothesis on the field extension
is needed in this case.

`SplitPinning.emptyEvenChainData` uses the empty index type `PEmpty`, so all of
its path and modified-root fields are given by elimination of an empty index.
`emptyEvenChainRestEquiv` identifies its remaining roots with all the simple
roots. Every ordering of them is middle-out, since there is no selected path.
`emptyEvenChainOrdering` uses the published contiguous enumeration of actual
simple-root Galois orbits.

`GaloisCompatiblePinningData.rationalRootFactor` is the rational root point at
a chosen coordinate times the canonical simple-reflection representative.
`rationalOrbitProduct` multiplies these factors in the orbit-block order.
Distinct orthogonal root factors commute by specializing the published
all-test commutation theorem to `Spec K`; uniqueness of the map to the terminal
object identifies the representative factors there with their rational points.
Transport of each factor follows from whole-root-map compatibility at arbitrary
rational coordinates and the published transport of canonical representatives.

For each orbit block, the root permutation induces a list permutation, and the
transported coordinates are `PolynomialGalois.rootCoordinateConjugate` of the
original coordinates. Pairwise commutation inside that block makes its product
invariant under the permutation, using `List.Perm.prod_eq'`. Different orbit
blocks retain their original order; the proof does not require factors in
different blocks to commute.

`emptyEvenChain_patternProduct` identifies the empty-path pattern product with
this orbit product. Reindexing the remaining coordinates by the orbit ordering
then supplies explicit witnesses for stability of the pattern set under every
rational Galois conjugation. The final existence theorem packages these witnesses
with the empty path family and its vacuous middle-out condition.

The construction uses the actual rational-point groups of the base-changed
scheme and normalized root maps from `D`. It adds no restriction on field
characteristic, perfectness, infinitude or simple connectedness. The additional
orthogonality hypothesis is essential to the scope of this helper and is not
claimed for arbitrary pairing-compatible pinnings.
