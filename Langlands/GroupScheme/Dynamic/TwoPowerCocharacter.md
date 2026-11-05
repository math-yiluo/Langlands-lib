# Internal two-power unitarization of cocharacters

This internal construction by Worker 1655 develops the finite-support
comparison needed to apply internal unitarization to an actual cocharacter.
It retains a closed star-stable matrix realization as an input.
The unconditional archimedean existence statement remains open.

`hermitian_projectors_of_normal_separating_support` applies the existing
normal-matrix projector criterion to the subtype of a finite support.
Off that support the projectors are zero, hence Hermitian. Consequently
the eigenvalues need only be distinct on the support.

`exists_two_power_unit_separating` bounds the absolute values of a finite
set of integer exponents by their finite supremum. It chooses a power of
two larger than twice that bound, and a primitive root of that order in
an algebraically closed `RCLike` coefficient field. Equal powers of the
root imply that its order divides the difference of the exponents. The
absolute value of that difference is smaller than the order, so it is
zero. The root is returned as an actual scalar unit.

The provenance is the implemented finite-projector and primitive-root
argument. The coefficient universe is unrestricted. No compact subgroup
or Iwasawa decomposition is assumed by these helpers.

`hasHermitianWeightProjectors_of_normal_separating_unit` applies the
finite-support criterion to the published actual Laurent projectors.
The actual cocharacter evaluation acts on each projector by the corresponding
integer power of the chosen scalar unit.

`weightProjector_innerIso_baseOfMatrix` computes every Laurent projector
after an actual base-point inner automorphism. The proof takes coefficients
of the published universal Laurent-matrix conjugation identity; constant
left and right matrix factors pass through coefficient extraction.
It follows that conjugation introduces no new weight. The separate
base-field evaluation identity compares the actual cocharacter point maps
under the same conjugation.

`HasInternalHermitianConjugate χ H` means that there is `g ∈ H` such that
the actual cocharacter conjugated by the base point of `g` has Hermitian
Laurent projectors. `hasInternalHermitianConjugate` proves this proposition
over an algebraically closed `RCLike` field when `H` is polynomially defined
and stable under conjugate transpose and contains the base-field evaluations
of `χ`. Choose the separating two-power root from the original support.
Its cocharacter value has that two-power equal to the identity. The internal
unitarization theorem supplies `g ∈ H` conjugating that value to a unitary
matrix, hence a normal matrix. The conjugated support is contained in the
original support, so the same scalar unit separates its weights. The
finite-support normality criterion makes those weights Hermitian.

For actual group schemes, `conjugate_baseOfMatrix_range_eq_of_mem` shows
that conjugation by an element of a representation's base-field image
preserves that image. It lifts the conjugator to a group point and uses
conjugation and its inverse on actual points. Thus the image retains its
star stability even though the conjugating matrix need not itself be
unitary.

`exists_internal_conjugate_hermitian` applies this construction to an actual
closed matrix representation and any actual cocharacter into the group.
The representation image is polynomially defined by the published image
equations theorem. Actual cocharacter evaluations lie in that image by the
published point-map comparison. The result supplies an internal matrix
conjugator and Hermitian weights for the composite with the conjugated
representation.

This construction neither supplies the initial closed star-stable
realization of an arbitrary reductive group nor handles real descent.
It also does not itself assemble the parabolic and Levi decomposition.
Those obligations remain in the host task; the present unit supplies
cocharacter compatibility inside an existing complex realization.
