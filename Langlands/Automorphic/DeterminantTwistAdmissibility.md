# Admissibility of actual determinant images

For a finite-order Hecke character of an actual number field, the existing
finite adelic and completed-local determinant characters are locally constant
and have open kernels. The number field has arbitrary universe and these
claims hold in every natural rank. The topologies are the existing finite
adelic and completion matrix topologies. Local constancy follows from the
published finite-order character theorem by continuous pullback along the
actual idele-class, determinant and factor maps. Openness of each kernel is
openness of the fiber over one.

For both an actual finite adelic realization and an actual completed-local
realization, `determinantTwist_isAdmissible_iff` proves preservation and
reflection of admissibility under the existing actual multiplier image.
The proof first uses the genuine equivalence from the scalar-twisted action
to that image, then applies the published open-kernel scalar-twist
admissibility theorem over the Noetherian coefficient field `ℂ`.
No target admissibility premise is required.

For each actual irreducible admissible local realization in positive rank,
`LocalRealization.determinantTwistPadicObject` constructs its actual
multiplied image as an object of the existing canonical p-adic correspondence
category. Irreducibility follows from the previously proved actual
invariant-subspace transport; admissibility follows from the new equivalence.
The published equality between completion and canonical p-adic topologies
supplies the required canonical-topology properties through `padicObject`.
`determinantTwistPadicClass` takes its class under genuine representation
equivalence. These objects retain the actual multiplied form-space
representative, in the number-field universe.

Provenance is internal composition of the published finite-order character,
actual multiplier, scalar-twist admissibility, representation equivalence
and canonical p-adic category constructions. No spectral existence,
factorization, Satake classification or global association is asserted.
