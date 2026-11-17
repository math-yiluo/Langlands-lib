# Actual finite frames from the classified Grassmannian quotient

This internal unit removes the separate fixed-rank frame-cover premise from
the actual determinant ampleness criterion for an affine Grassmannian
classification.

Let `D : Module.Grassmannian.ProjectiveEmbedding.Rep R E k` be the existing
quotient Grassmannian representation, let `f : X ⟶ D.Gr` be a scheme
morphism, and let `N` be an actual module sheaf on `X` with a prescribed
family `q : E → Γ(N, ⊤)`. Assume `HasAffinePointComparison D f N q`: on
every affine open the actual section module is linearly isomorphic to the
classified quotient, and the isomorphism preserves the specified quotient
generators.

`sectionFamilyMap` forms finite linear combinations of the restrictions of
`q (x j)` for a Grassmannian chart family `x : Fin k → E`. On an affine
subopen of `f ⁻¹ᵁ D.V x`, the existing `basis_test_iff_preimage` says that
this linear map is bijective. Transporting the standard function-space
basis across the resulting linear equivalence gives `sectionFamilyBasis`;
its basis vectors are exactly the restricted prescribed sections.

`comparisonFrame` constructs an actual finite free sheaf frame on the
whole chart preimage. The prescribed global sections restrict to the
computed bases on every affine subopen, so `affineBasisFrame` applies.
No affineness of the whole chart preimage is required for this construction.
The Grassmannian chart preimages cover `X`; `comparisonFrames` packages
them as actual `FiniteLocalFrames` of the fixed standard rank `k`.
`hasFiniteLocalBasis_of_affinePointComparison` records the resulting
finite local basis property. It requires neither a pre-existing freeness
witness nor a separate rank premise.

For compact `X` and affine `f`, the theorem
`finiteLocallyFreeDeterminant_isAmple_of_affinePointComparison` proves
ampleness of the existing actual chosen determinant for any supplied
finite-basis witness `hN`. It supplies the constructed frames to the
existing actual Grassmannian determinant ampleness criterion. The witness
`hN` may itself be obtained from the preceding theorem; no independent
constant-rank frame cover is an input.

The provenance is internal: the existing actual affine-point quotient
comparison gives the basis test, the specified sections give actual free
frames, and the existing actual determinant criterion gives ampleness.
This unit does not construct the classified quotient comparison or prove
that a particular parabolic jet module satisfies it.
