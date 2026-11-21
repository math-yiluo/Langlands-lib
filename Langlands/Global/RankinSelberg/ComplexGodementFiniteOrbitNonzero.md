# Finite unitary orbit and nonvanishing of the continued Godement integral

`ComplexGodementFiniteOrbitNonzeroStatement` applies to a continuous slice
of a family with a uniform simple-root bound. If that slice is nonzero
somewhere on the smaller complex general linear group, at any adjoining
exponent there is a rectangular Schwartz test with nonzero continued
Godement value at the identity. Its support is compact and consists of
full-row-rank matrices, and the span of its right unitary translates is
finite-dimensional.

`complexGodementFiniteOrbitNonzero` starts with the localized nonzero test
from `ComplexGodementLocalizedNonzero`. It averages the test over the
unitary group with weights polynomial in the unitary entries and their
conjugates. The weighted averages are Schwartz by the compact averaging
theorem. Their supports lie in the compact unitary saturation of the
original support, where right multiplication by an invertible matrix
preserves row rank. Left invariance of compact Haar measure moves a
right translation of the averaged test onto the weight. The polynomial
in the translated unitary argument has separated variables, which puts
all translates of the averaged test in a finite-dimensional span.

At a fixed smaller matrix, the column integrand of the average has
compact support in the column and unitary variables. The proof obtains
this compact set by projecting the saturated support to the last column
and applying the inverse of the smaller matrix. Fubini then commutes the
column integral with the compact average. The translated kernel bound
controls the outer integral uniformly on the compact group, so another
application of Fubini commutes that integral with averaging. The integral
of the translated kernel varies continuously on the unitary group by
continuity of the continued Godement value and division by its nonzero
determinant factor. If every polynomial average had value zero, this
continuous function would pair to zero with every polynomial weight.
Polynomial density would force it to vanish at the identity, in conflict
with the localized test.

This is an internal nonvanishing argument for the continued integral in
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §7.2, formulas (7.6)
and (7.7) on p. 48. It uses the compact group to produce a test in the
class used by the finite-orbit Godement construction.
