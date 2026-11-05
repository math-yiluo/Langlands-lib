# Common support from a norm-kernel level and central Cartan charts

This internal adapter combines a supplied `NormKernelCompressionLevel` and
a supplied ambient central Cartan cover for its exact orthant. It constructs
actual Hecke sandwich data on the common rational-character norm kernel and
deduces uniform coefficient support at the prescribed open level. It retains
existence of the level and the Cartan cover as separate hypotheses; it does
not prove the unconditional uniform-support target.

`NormKernelCentralCartanCover d K0` records a finite residual set in the actual
ambient rational-point group. Every element of the actual norm kernel has
the literal ambient expression
`k₁ * (d.orthantHom(n) * f) * k₂ * z`, with both compact factors in the supplied
`K0`, the residual in that finite set and `z` in the full abstract center.
The orthant is precisely the one retained by the common-level record.
No cover outside the norm kernel is required by this interface.

The canonical point topology on the ambient rational points and its inherited
topology on the actual norm kernel are used throughout. For connected reductive
`G`, compactness places `K0` inside that kernel. The record's normalizer
condition therefore implies that `K0` normalizes the image of the kernel level
under the actual inclusion. This is `ambient_normalized`, proved by mapping
the retained normalizer inclusion using `Subgroup.le_normalizer_map`.

`nonempty_sandwich_of_centralCartanCover` applies the existing
`exists_rationalNormKernel_residual_cover` with this image level. Its compact
normalizer adjoins the compact intersection of the norm kernel with the full
center. The finite central residual representatives lie in the actual kernel,
and the resulting decomposition uses the same kernel-valued orthant.
Injectivity of the kernel inclusion identifies the image level's preimage with
the original level, so the descended compact subgroup normalizes that very
level. The existing finite-residual Iwahori sandwich theorem then uses the
record's ordered minimal-face factorization, whole-orthant positive-monoid
membership and forward Levi preservation. Residual elements need not normalize
the level or commute with the orthant.

`sandwichOfCentralCartanCover` selects these actual Haar Hecke sandwich data
before any representation. `hasUniformSupport_of_centralCartanCover` applies
the existing sandwich-to-support theorem on the norm kernel itself. That
theorem bounds the actual compact irreducible classes at the level and uses
finite fixed bases and averaged coordinate functionals to obtain one compact
support. The representation-carrier universe is independent of the field
universe. Finally, since the common level is contained in the prescribed `U`,
every `U`-fixed vector and `U`-invariant algebraic-dual functional is fixed at
the smaller level; the same compact set proves the desired support bound at
`U`. The coefficient is the existing inverse coefficient, and its functional
is drawn from the entire stated algebraic dual with the prescribed invariance.

The field has arbitrary characteristic, and an empty simple-root type is
allowed. No representation extension, finite restriction, admissibility,
coefficient bound or finiteness premise enters this adapter. The measurable
space on the kernel is assumed Borel, and the measure is left Haar.

The provenance is internal assembly of the supplied common geometry, compact
central residual descent, actual finite-residual Hecke multiplication and
the finite-class support construction. The ambient cover and simultaneous
basis still require their own geometric existence proofs, and this conditional
construction leaves the exact uniform-support statement and its imports
unchanged.
