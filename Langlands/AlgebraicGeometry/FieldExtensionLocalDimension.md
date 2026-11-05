# Local dimension under extension of the ground field

`finiteTypeFieldExtensionLocalDimensionInvariance` proves the exact
published proposition `FiniteTypeFieldExtensionLocalDimensionInvariance`.
Worker 105 wrote the proof; Worker 1604 checked and prepared it for
publication.

The fields k and K and the commutative finite-type k-algebra A have three
independent universes. For every prime q of K ⊗[k] A, its local dimension
equals that of its contraction along the actual inclusion a ↦ 1 ⊗ a.
Local dimension is the minimum of dimensions of open neighbourhoods,
as defined in `LocalTopologicalDimension`, with values in `WithBot ℕ∞`.
The extension K/k may be transcendental, infinite or inseparable; A may
be reducible or nonreduced. The zero algebra is included and has no primes.

Choose a principal neighbourhood of the contracted prime whose dimension
equals its local dimension. Its inverse image is the basic open of the
actual tensor element `1 ⊗ r`, and the chosen upstairs prime lifts to that
principal localization. Open embeddings preserve local dimension.
Local dimension there is bounded by the total dimension of the
localization. Mathlib's actual tensor/localization equivalence and total
dimension invariance under extension of the field identify this total
dimension with that of the chosen downstairs principal neighbourhood.
The principal localization is still finite type over k. This proves
`topologicalKrullDimAt_tensorProduct_le`.

For the reverse inequality, put the field in the right tensor factor.
Mathlib proves that the contraction map from this tensor product is
open. It is flat by base change from the ground field. The flat open
spectrum-map argument in `FlatOpenLocalDimension` supplies the lower
bound. Tensor commutation, its actual spectrum homeomorphism and the
commuting inclusion maps transfer both bounds to either tensor order.
The equalities are exposed as `topologicalKrullDimAt_tensorProduct_eq`
for A ⊗[k] K and `topologicalKrullDimAt_tensorProduct_includeRight_eq`
for K ⊗[k] A. Introducing the quantified fields, algebra and prime then
proves the exact proposition.

The total-dimension step imports
`finiteTypeFieldExtensionRingDimensionInvariance` from
`FieldExtensionDimensionProof`. The chain-lifting and flat open-map
inequality are implemented in the accompanying `FlatOpenLocalDimension`
module.

The registered Stacks source is
`stacks-fibre-constructibility-local-dimension-2026-11-04`,
SHA-256 `1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
file `02FW.html`, Lemma 29.29.3(1), with the local-dimension convention
in `0055.html`, Definition 5.10.1. The proposition is the affine
specialization of that base-change equality to Spec A over Spec k and
Spec K → Spec k. The implemented proof uses principal neighbourhoods,
total dimension invariance and going down. General scheme base change,
sublevel retrocompactness and filtered fibre descent retain their
separate proof obligations.
