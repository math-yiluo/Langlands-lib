# Simultaneous lifts of finitely many fibre sections

`FibreNeighbourhoodLifts f s M σ` records one affine open neighbourhood
of the arbitrary point `s`, actual sections of `M` over its inverse
image, and exact equality of their canonical fibre restrictions with
the indexed sections `σ`. The definition retains the actual
scheme-theoretic residue-field fibre and the specified module sheaf.

For a finite index type, `nonempty_fibreNeighbourhoodLifts` proves that
individual neighbourhood lifts give this common data. The proof
chooses each neighbourhood and lift, intersects the finitely many
neighbourhoods, and takes an affine open refinement containing `s`.
It restricts each original section to that refinement. The compatibility
lemma `fibreNeighbourhoodSection_restrict` proves that its fibre
restriction is unchanged. This also handles an empty index type,
when the intersection is the whole base and an affine neighbourhood
of `s` still exists. `finiteFibreNeighbourhoodLifts` chooses this data.

`ProperFibrePowerSectionLiftingStatement.finite_family` applies this
construction in every degree above the uniform threshold supplied by
the stated single-section lifting proposition. Its hypothesis is that
proposition itself: this lemma does not prove the missing cohomological
lifting theorem. The family and degree may vary; all sections of any
one finite family lift over one common affine neighbourhood. It does
not raise sections to higher powers or assert anything about their
generation opens.

This is an internal construction from finite intersections, the affine
open basis of a scheme, and functoriality of the canonical fibre
restriction. No additional result from external literature is assumed.
