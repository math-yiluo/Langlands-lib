# Tensor presentations of specified finite automorphic realizations

This internal construction connects the published actual finite adelic tensor
action with a **specified invariant subspace of actual automorphic forms**.
It records a genuine equivariant linear equivalence, constructs its faithful
form-valued map, and compares the whole local restriction and its individual
slices. Existence of such a presentation for a general automorphic space is
not asserted.

## Inputs and provenance

The field `F : Type uF` is a number field. The matrix rank `n : ℕ` is arbitrary;
no positivity assumption is used. The coefficient field is `ℂ`. For each finite
place `v`, the carrier `V v : Type uV` is a complex module with an additive
commutative group, and `ρ v` is a representation of the actual completed-local
matrix group `FiniteLocalGL F n v`. The field and model universes are independent.
No topology or finite-dimensionality is required on the vector carriers.

The finite exceptional set is `E`, and the family `e` has vectors in all
carriers. The supplied law `he` says that `e v` is fixed by every element of
the actual local integral subgroup when `v ∉ E`. Values of `e` at places in
`E` need not be nonzero or integral-fixed. The published tensor action on
`RestrictedTensor.Space ℂ V E e` uses these data.

The target `S : FiniteRealization F n` is an actual invariant subspace of the
published `AutomorphicForms F n`, acted on by positive right translation.
It is not a replacement carrier satisfying an automorphic occurrence axiom.
Its inclusion into forms and its smooth finite adelic action are already
constructed in `FiniteRealization.lean`.

This module has internal provenance, with no new external-literature assertion.
It uses the genuine tensor separation from
`Global/FiniteAdelicGL/LocalTensorSeparation.lean`, the form-valued tensor maps
from `TensorRealization.lean`, and the actual slice images and equivalences
from `LocalRealization.lean`. All newly proved claims follow by composition,
surjectivity, equality transport, or algebraic tensor induction.

## Presentation data and its exact image

`FiniteTensorPresentation F n ρ E e he S` has two fields:

- `reference_nonzero` proves `e v ≠ 0` outside `E`.
- `equiv` is a genuine representation equivalence from
  `tensorRepresentation F n ρ E e he` to `S.representation`.

The second field includes a bijective complex-linear map and the finite adelic
intertwining law. The structure is data, not a proposition or a proof that every
realization has a tensor decomposition. In particular, nonzeroness of the
reference vectors alone is not used to infer existence of this equivalence.

For a presentation `P`, `toMap` composes `P.equiv` with the actual inclusion
`S.inclusion`. The lemma `toMap_injective` composes the injectivity of those two
maps. The exact formula is

```text
P.toMap x = S.inclusion (P.equiv x).
```

The theorem `image_toMap` proves equality of embedded invariant subspaces:
`finiteRealizationImage F n P.toMap = S`. One inclusion follows from membership
of each `P.equiv x` in `S`; the reverse uses the surjectivity of `P.equiv` on
each actual subtype vector of `S`.

Conversely, `ofMap` takes nonzeroness of the reference vectors, a form-valued
tensor intertwiner `T`, injectivity of `T`, and the equality of its actual
image with `S`. It uses the published equivalence onto the range of an
injective map and transports the result along that equality.

`HasFiniteTensorPresentation` is the proposition that this data type is
nonempty for the **specified** `V, ρ, E, e, he, S`.
`hasFiniteTensorPresentation_iff` proves its equivalence with nonzeroness
outside `E` and existence of a faithful tensor map having exactly image `S`.
This is an equivalence of two descriptions of presentation existence; it is
not a theorem supplying either side for arbitrary input.

## Whole local restriction and actual slices

`restrictedEquiv v` keeps the same bijective linear map and restricts its
intertwining law along the actual identity-supported local insertion.
It compares the entire tensor carrier with the entire carrier of `S`.

`LocalEquivalence` is a type alias for the comparison

```text
separatedLocalRepresentation F n ρ E v e ≃ S.localRepresentation v.
```

The source has underlying space
`V v ⊗[ℂ] LocalTensorTail F E v e`, with the local group acting on the first
factor alone. `localEquiv v` constructs this equivalence by composing inverse
tensor separation with `restrictedEquiv v`. The original exceptional places
other than `v` remain in the complementary tensor construction. No
one-dimensionality of that complementary space is assumed or concluded.

`inclusion_localEquiv` proves that inclusion into forms after this equivalence
is exactly the published `FiniteTensorRealization.localMap` for `P.toMap`.
Thus the comparison is tied to the actual form-valued realization.

For any complementary vector `y`, `slice v y` is the actual locally invariant
range of the map

```text
x ↦ P.toMap (inverseLocalSeparation (x ⊗ y)).
```

`slice_le` places this subspace inside `S.toLocal F n v`, using the published
slice containment and `image_toMap`. Neither this containment nor the definition
requires `y ≠ 0`. When `y` is nonzero, `sliceEquiv` uses the proved injectivity
of `P.toMap` and the published faithful-slice construction to give a genuine
equivalence from `ρ v` to the action on the actual slice.

`toLocal_le_iff_slices_le` characterizes the whole local restriction by all its
slices: for every actual local invariant form subspace `L`,

```text
S.toLocal F n v ≤ L  ↔  ∀ y, P.slice v y ≤ L.
```

The forward direction composes containment with `slice_le`. For the reverse,
surjectivity of `localEquiv v` writes any vector of `S` as the image of a tensor.
Tensor induction reduces to pure tensors, which lie in their corresponding
slices, and sums, which remain in `L` because it is a submodule. This is a
generation property for the family of all slices; it does not identify a
single slice with the whole local restriction.

Finally, `slice_isoClass_eq` compares presentations `P` and `Q` with the same
`V, ρ, E, e, he`, possibly into different actual finite realizations `S` and
`S'`. For nonzero complementary vectors `y, y'`, it composes the inverse
`P.sliceEquiv` with `Q.sliceEquiv` and applies the existing local-class equality
criterion. The two compared carriers are subtypes of forms in universe `uF`,
so their smooth isomorphism classes lie in the same quotient universe even
when the model universe `uV` differs.

## Scope

The input tensor data and a global equivalence are explicit. This module
does not construct a presentation for a general finite realization, choose
nonzero complementary vectors, or prove uniqueness across different local
factor families. The local-class comparison concerns copies of the same
specified factor and does not identify embedded form subspaces.

Irreducibility, admissibility, one-dimensional integral-fixed spaces, normalized
Satake data, full archimedean stability, and the automorphic factorization and
uniqueness theorems remain separate obligations. Embedded character and
cuspidal conditions can be applied through the exact image equality and the
published slice-containment lemmas; no descent of those conditions to a local
isomorphism class is claimed here.
