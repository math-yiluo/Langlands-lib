# Reduction of torsion-configuration determination to two geometric inputs

`torsionConfigurationDetermination_of_cubicFieldEmbedding` proves the
conditional implication from `CubicFieldEmbeddingStatement` and
`CubicBundlePolarizationDeterminationStatement` to the unchanged
`TorsionConfigurationDeterminationStatement`, in the same universe. The
module does not discharge either geometric premise.

## From evaluations to embedded images

`Datum.TorsionConfigurationEquivalent.exists_cubicEmbeddings` transports a
basis of the first datum's full cubic linear system to a basis of the
second using the isomorphism of cubic direct images on global sections.
The published cubic fibre rank gives `cubicProjectiveDimension g d + 1`
sections. The supplied Lefschetz statement gives generation and closed
immersions, and the published linear-system twist comparison gives the
actual cubic bundle on each source. At a labelled point the commuting
evaluation equation becomes the equality of pulled-back basis sections
under the given isomorphism of the two fibre lines. The relative
linear-system map commutes with those pullbacks and is invariant under
the isomorphism carrying the sections. Thus the two actual projective
point maps agree for each label, not just their zero patterns.

The common cutoff and the cubic-power torsion bound, as assembled in
`exists_cubicEmbedding_ker_eq_of_torsion`, now give equality of kernel ideal
sheaves. The cutoff uses the fixed polynomial `6^g d T^g`; the point bound
is linear in the tested degree. The resulting level bound is uniform in
the field, the level, and the two data with fixed `g,d`.

## From the common kernel to the datum

`Datum.IsCubicEmbedding.nonempty_polarizedIso_of_ker_eq` works over a
locally noetherian base on the supplied closed immersions. Equal kernels
give the scheme isomorphism over the base. Cancelling the second closed
immersion shows that the isomorphism preserves every labelled point; the
zero label preserves the identity and the unit coefficient labels give
preservation of the ordered level sections. Pointed-morphism rigidity
makes the isomorphism an abelian-scheme isomorphism. Pulling back the same
projective twist shows that the cubic bundles correspond without a base
twist. In applying the supplied polarization determination statement,
the base line is the structure line bundle.

The argument is an internal reduction. The reconstruction step uses the
parts of the argument on printed p. 131 of Mumford–Fogarty–Kirwan,
*Geometric Invariant Theory*, 3rd ed., that recover the abelian group law,
level and polarization from a cubic embedding with labelled points. It
does not recover a linear rigidification, and the preceding
configuration-to-image step is not asserted in that source. The explicit
conditional conclusion is not an unconditional proof of
`TorsionConfigurationDeterminationStatement`.
