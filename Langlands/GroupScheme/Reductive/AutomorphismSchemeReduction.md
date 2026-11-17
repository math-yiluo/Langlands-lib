# From relative automorphism geometry to clopen inner-action loci

This internal reduction assumes the two published existence propositions
`ReductiveAutomorphismSchemeGeometryStatement` and
`ReductiveRelativeAdjointQuotientExistenceStatement`. It constructs the full
automorphism group scheme supplied by the first premise and proves its
inner-action classifier clopen. It neither proves the geometric existence
premises nor gives an unconditional proof of the inner-action-locus target.

`ReductiveAutomorphismSchemeGeometryStatement.automorphismScheme` chooses
the full self-Isom representative supplied by that premise and equips its
unchanged parameter scheme with the represented automorphism group
structure. The representative depends on the base, the reductive group
and the geometry premise, and not on a subsequently supplied quotient.

For an arbitrary supplied full-centre fppf quotient `p : G → Gad`,
the target `Gad` is not assumed affine or reductive.
The second premise supplies one reductive full-centre quotient.
The universal comparison of full-centre quotients identifies `Gad` with
that reductive target; invariance of reductivity under isomorphism makes
`p` an `IsRelativeAdjointQuotient`. The compatible supplied action `c`
then equals its canonical inner action by uniqueness.

The geometry premise supplies an outer quotient for that canonical action,
with étale separated outer parameter. The generic identity-orbit argument
identifies the direct action classifier with inversion followed by its
outer identity orbit. The orbit is open and closed, and inversion is an
isomorphism. This proves `automorphismScheme_clopen` and hence
`reductiveAutomorphismScheme_of_geometry`.

Finally, `reductiveInnerActionLocus_of_geometry` accepts the published
affine quotient-existence proposition, converts it to reductive quotient
existence, and applies the preceding reduction and the published
automorphism-scheme-to-inner-locus reduction. Its conclusion is the unchanged
`ReductiveInnerActionLocusStatement` in every universe, conditional on the
two explicit existence premises. All base schemes, supplied quotient targets,
acting groups and test groups retain their original scope.
