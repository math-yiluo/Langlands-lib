# A single torus criterion for right standard compact invariant kernels

This internal module develops the passage from a single inverse-modulus
weighted diagonal integral to the compact-uniform hypothesis of the actual
Whittaker quotient criterion.

The diagonal modulus is continuous because it is the finite product of the
continuous idelic absolute values of the positive roots. Right translation
of the torus variables by a fixed diagonal tuple multiplies the weighted
integral by that tuple's modulus. The proof uses the multiplicativity of
the modulus and translation invariance of Haar measure. This identity
holds for arbitrary extended nonnegative kernels, without a measurability
or finiteness assumption.

`IsRightStandardCompactInvariant` means invariance under right multiplication
by the actual standard compact subgroup, transported to adelic group-scheme
points. For a kernel with this invariance and left invariance under the full
adelic upper unipotent subgroup, an Iwasawa factorization of a right
translate removes its unipotent and compact factors. Diagonal conjugation
preserves the unipotent subgroup, so the remaining factor acts by translation
of the diagonal parameters.

For every compact set of right translates, the imported compact Iwasawa
parameter theorem supplies one compact set of possible diagonal factors.
The continuous modulus has a finite upper bound on that set. Multiplying
this bound by the single weighted diagonal integral proves
`compactTorusBound_of_single`. This implication needs no measurability of
the kernel.

Finally, `lintegral_whittakerQuotient_lt_top_of_single` applies the imported
compact-uniform criterion for the defined Whittaker quotient measure.
This step assumes measurability of the kernel and compactness of the additive
adelic quotient, as required by that criterion. It allows every natural rank
and every Haar normalization on the full diagonal idele torus.

The construction is derived from the imported actual diagonal modulus,
compact Iwasawa parameter theorem and quotient integration criterion.
It makes no new attribution to the literature and asserts no unconditional
gauge convergence without its single finite diagonal integral premise.
