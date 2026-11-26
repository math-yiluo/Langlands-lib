# Real-place reduction with the rank-one equal case proved

`RealPositiveJacquetRestrictionEquationStatement` gives the local analytic
premises in Jacquet's conventions for unequal ranks and for the equal rank
\(r+1\) with \(0<r\). The equal-rank premise is expressed separately by
`RealPositiveEqualJacquetRestrictionEquationStatement`. Both use actual
cuspidal Whittaker restrictions, the supplied real place, additive character
and compatible quotient measures, and the supplied parameters of the original
and contragredient realizations. The equal-rank equation also uses a Schwartz
function on the last-row space.

`realEqualAtRank_zero` proves the equal-rank equation at rank index zero by
`Langlands.LocalFactor.RealTate.realArchimedeanTateStatement`. The rank-zero
comparison identifies the actual restrictions with the two local characters
and the compatible quotient measures with multiplicative Haar measures.

`realEqualFunctionalEquation_of_positiveJacquet` uses this Tate case in rank
one. In higher equal ranks it reflects the dual integral with
`realEqualDualReflection` and changes the epsilon factor to the required
character using the parameter-determinant and compact-scalar comparisons.
`realPlacePositiveAnalyticReduction` uses that theorem for its equal-rank
conclusion and the same parameter-determinant comparison for the unequal-rank
sign. These conversions preserve the field universe \(u\).

The source equations are those of H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), Theorem 2.1, author-posted p. 6. The rank split and the
conversion of the negative Fourier convention are derived from the
Library's real Tate theorem and `realPlaceJacquetConventionReduction`.
