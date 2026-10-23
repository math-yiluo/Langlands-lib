# Local separation of finite adelic tensor representations

This module exposes a chosen completed-local factor in the constructed finite
adelic tensor representation by a genuine equivalence of representations.
It combines the algebraic equivalence in
`Langlands.Representation.RestrictedTensor.Separation` with the actual local
inclusion action in `Langlands.Global.FiniteAdelicGL.RestrictedTensor`.

## Data and scope

The number field `F`, coefficient field `K`, and family of local vector spaces
`V` have independent universes. The matrix rank `n` is any natural number.
For each finite place `v`, `ρ v` is a representation of the actual matrix group
`FiniteLocalGL F n v` on `V v`. Let `E` be a finite set of places and `e` a
reference family. The action requires that `e v` be fixed by the actual integral
subgroup outside `E`. Separation additionally requires `e v ≠ 0` outside `E`;
there is no nonzero condition at exceptional places.

`LocalTensorTail F E v e` is the existing algebraic restricted tensor space over
places different from `v`. Its exceptional set is `tailSet {v} E`, so it retains
all exceptional places other than the separated place. No completion or topology
on a vector space is introduced.

## The local representations and equivalence

`tensorLocalRepresentation` restricts `tensorRepresentation` along the actual
identity-supported homomorphism `localInclusion F n v`. `TensorLocalAction` is
a compact name for its representation type.

`separatedLocalRepresentation` is Mathlib's tensor product of `ρ v` and the
trivial representation on `LocalTensorTail`. The formula
`separatedLocalRepresentation_tmul` says that its action sends
`x ⊗ y` to `ρ v g x ⊗ y`.

`localSeparation_intertwines` proves that the published algebraic
`localSeparation` intertwines these two actions.
`localTensorSeparation` bundles that linear equivalence and this identity as a
`Representation.Equiv`. Its underlying linear map and inverse are the existing
separation and reassembly maps, rather than chosen maps supplied as assumptions.

`localTensorSeparation_pure` gives the exact elementary-tensor formula on a
stage containing `v`: separate its `v` coordinate and retain every other
coordinate in the complementary stage. `tensorLocalRepresentation_reassemble`
states that local insertion on the reassembly of `x ⊗ y` equals reassembly of
`ρ v g x ⊗ y`, for arbitrary vectors `x` and complementary tensors `y`.

`restrictedLocalTensorSeparation` supplies the same equivalence for
`restrictedTensorRepresentation`, using `ReferenceVectors`. Its nonzero
condition follows from `ReferenceVectors.family_nonzero`; the unused reference
coordinates at exceptional places can still be zero.

## Implemented proof and provenance

This is an internal construction from published Library results. To prove the
intertwining identity, `hom_ext_cofinal {v}` reduces equality of linear maps to
elementary tensors on stages containing `v`.
`tensorRepresentation_localInclusion_pure` changes only that coordinate.
The two `localSeparation_pure` formulas then agree: `Function.update_self`
handles the separated coordinate, and `Function.update_of_ne` leaves every
complementary coordinate fixed. The inverse-action formula follows from the
intertwining law of the inverse representation equivalence.

No new assertion from external literature is used. This unit identifies local
actions of a tensor representation already constructed from supplied factors.
It does not assert that an automorphic representation admits such a
factorization, that the factors are irreducible or admissible, or that local
components are uniquely determined. In particular, the full local restriction
has the complementary tensor as a multiplicity space; it is not identified with
the single factor `V v`.
