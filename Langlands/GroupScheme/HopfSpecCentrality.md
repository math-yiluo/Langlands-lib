# Centrality of spectra of Hopf algebra maps

This internal extension of `HopfSpecPoints` and
`CentralExtensionHopfSpec` compares actual group-scheme centrality with
coordinate coactions. The commutative base ring R and the two commutative
Hopf algebras A and C lie in any common universe u. No finiteness, flatness,
smoothness, or surjectivity hypothesis is used in the comparison.

For a Hopf algebra map π : A → C, `isCentral_of_specPoint_commute` proves
centrality of Spec π if its C-valued point images commute with all A-valued
points, over every commutative R-algebra Y in the same universe. The product
of the two Hopf spectra over Spec R is affine. Choose a presentation of it
as the spectrum of an R-algebra and apply the assumed pointwise commutation
to its two projections. Cancellation of the presentation isomorphism gives
commutation of the universal pair. The existing
`ArtinianCentrality.isCentral_of_universal_commute` then gives the full
`IsCentral` predicate, including all restrictions of all test schemes.

`isCentral_of_rTensor_comul_eq` applies this point detector when, for every
a in A,

`(π ⊗ id) Δ(a) = flip ((id ⊗ π) Δ(a))`.

Applying the tensor evaluation map determined by any f : C → Y and
g : A → Y makes their two convolution products equal. Pure-tensor
induction identifies the two evaluations, and the Hopf-spectrum point
multiplication and composition formulas give the required commutation.
`isCentral_iff_rTensor_comul_eq` combines this reverse implication with
the existing forward implication in `CentralExtensionHopfSpec`.

If Spec π is monomorphic, `commGroupSchemeOfTensorCoactions` uses the
resulting centrality and the existing `IsCentral.commGroupScheme`
construction to bundle Spec C as a commutative group scheme.
`commGroupSchemeOfTensorCoactions_toGrp` is reflexive equality: the source
group scheme and all its operations are retained.

This module establishes the scheme/Hopf comparison. It does not derive
coaction equality from a nilpotent base reduction, or prove the
arbitrary-base fibrewise central-isogeny statement.
