# Actual CM images of finite and local automorphic realizations

This is an internal construction from the actual function pullback in
`AutomorphicCMTransport`, its cusp restriction in `CuspidalCMTransport`, and
the existing `FiniteRealization` and `LocalRealization` carriers. It does not
identify a new literature-defined object. All fields and completions, adelic
matrix groups, invariant function subspaces and group transport maps are the
existing actual constructions.

For number fields `K : Type uK` and `L : Type uL`, independently quantified,
`AdelicGLTransport.finiteEquiv_localInclusion` proves that arithmetic finite
adelic transport commutes with the identity-supported local matrix insertion
at corresponding finite places. Projection at each place proves this: at the
specified place the projection is the transported matrix, and elsewhere it
is the identity. Injectivity of the place equivalence distinguishes the cases.
This supplies the actual local covariance needed below.

Now let `K` be a CM number field in any universe and `n` any natural matrix
rank. Write `c` for `CMConjugation.fieldConj K`, and write `cv` for
`AdelicFunctoriality.finitePlaceEquiv c v`. This is the pulled-back prime
ideal, with ideal membership `x ∈ cv` equivalent to `c x ∈ v`. The existing
actual completion group equivalence
`AdelicGLTransport.localEquiv n c v` goes from the matrix group at `cv` to
that at `v`. The theorem `AutomorphicForms.complexConj_localRightAction`
uses exactly this direction: CM pullback of a form translated at `v` by the
transported matrix equals translation of the pulled-back form at `cv`.

For both finite adelic and local realizations, `complexConj` takes the actual
linear image of the embedded form subspace under
`AutomorphicForms.complexConj n`. The local construction sends a subspace
invariant at `v` to one invariant at `cv`. Image and preimage, together with
covariance and the inverse group equivalence, construct
`complexConjOrderIso` on the respective lattices. No preservation premise is
supplied. Restricting the existing continuous complex-linear function map
gives `complexConjEquiv` onto each actual image. Its forward and inverse
underlying maps both send `f(g)` to `f(CMConjugation.adelicConj K n g)`.
The complex values remain fixed. Continuity uses the inherited compact-open
continuous-function topology and its subtype topologies.

The representation covariance is proved for every finite adelic or local
matrix. `complexConjRepresentationEquiv` is the corresponding genuine
representation equivalence from the source representation precomposed with
the actual group map to the representation on the actual image. Its linear
map is precisely `complexConjEquiv`. Smoothness of the image representations
is inherited from the existing realization carriers.

The finite image is involutive as an embedded realization. For the local
construction, `complexConj_complexConj_toSubmodule` proves equality of the
actual embedded submodules after two applications. The statement does not
identify the dependent local group indices definitionally. The image order
equivalences reflect the zero subspace and preserve inclusions. The same
image/preimage argument on the restricted representation carriers constructs
`complexConjSubrepresentationOrderIso`, so irreducibility is preserved and
reflected. This is finite or local irreducibility as indicated by each
carrier, not irreducibility under all global operators.

Both constructions preserve and reflect the existing embedded global
central-character condition from `chi` to `chi.complexConj`; this uses the
existing argument-only character convention and the actual form membership
biconditional. With compactness of the scalar additive adele quotient
explicit, the existing actual normalized constant-term cusp condition is
also preserved and reflected. These predicates concern the embedded forms.
They are not asserted to transfer under arbitrary abstract equivalences.

`FiniteRealization.toLocal_complexConj` proves equality of the actual embedded
subspaces obtained by first taking the finite CM image and restricting at
`cv`, or first restricting at `v` and taking the local CM image. This is a
restriction of the whole finite carrier, not a tensor-factor local component.
No tensor presentation, spectral existence, unramified spectrum, occurrence,
classification, arbitrary representation-class operation or conjugate
self-duality assertion is supplied here.
