# Descent of split normalizer quotient models

`DiagonalizableNormalizerQuotientLocalModels` is an explicit input condition:
for every commutative ring and finitely generated abelian character group,
every supplied representative of the normalizer of a closed diagonalizable
subgroup of a smooth affine group has an actual quasi-affine homogeneous
quotient. This module does not assert that input unconditionally.

Given that input, `relativeMultiplicativeTypeNormalizerQuotientOfLocalModels`
constructs the actual quotient for every supplied normalizer representative
of a closed multiplicative-type subgroup over every scheme. The quotient is
smooth over the original base and quasi-affine above every affine base open.
The source group need not itself be smooth. All coset fibers retain the full
all-scheme-test homogeneous quotient meaning.

This is derived descent infrastructure. A supplied diagonalizable source over
a spectrum is compared with the literal group-algebra model; source
isomorphism preserves its range and hence its normalizer. Over an affine base,
compactness refines the multiplicative-type splitting fppf cover by a finite
family of actual affine spectra. Iterated base-change comparison transports
diagonalizability, and normalizer base change transports the supplied
representative. The ring-local input supplies local actual quasi-affine
quotients. The finite affine-family coset-sheaf descent constructor gives the
quotient over that affine base. Smoothness of the represented normalizer uses
the published multiplicative-type normalizer smoothness theorem.

Finally, actual full coset-sheaf models over affine base opens glue using
`HomogeneousQuotientSheaf.exists_quotient_of_affine_local_models`. This gives
smoothness and the asserted quasi-affine preimages over every affine base
open. Constructing the ring-local input remains an independent obligation;
this conditional adapter does not complete the host target by itself.
