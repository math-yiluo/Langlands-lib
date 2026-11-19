# Relative unit corestriction at finite quotient stages

Let \(\Omega/K\) be Galois, \(E\) a finite intermediate field,
and \(N\) an open normal subgroup in the fixing subgroup of \(E\).
Write \(M=\Omega^N\). The image of the fixing subgroup in
\(\operatorname{Gal}(\Omega/K)/N\) corresponds to the actual image
of \(\operatorname{Gal}(M/E)\) in \(\operatorname{Gal}(M/K)\).
This correspondence follows from restriction of automorphisms.
The two fixed-unit comparisons both identify invariant units with
the actual units of \(M\), keeping the underlying elements.

Naturality of ordinary transfer under the group and coefficient
identifications gives equality of the two transfer maps. The
Library's positive-degree comparison identifies ordinary transfer
on these cohomology groups with the relative field corestriction
implemented through Tate cohomology. Thus
`finiteCorestriction_fixedFieldCohomologyIso` computes the genuine
finite quotient transfer as the actual field-relative corestriction
after the quotient and unit identifications.

This is the finite-stage comparison for the cohomological
corestriction used in Serre, *Local Fields* (1979), Chapter XI,
§§1–2, printed pp. 166–168. The proof uses the Library's exact
ordinary transfer naturality and positive-degree Tate comparison.
