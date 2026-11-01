# Extending a line-bundle section from a global principal open

This internal helper extends an arbitrary section of an actual line bundle
over `D(f)`, for a global function `f`, after multiplying by a nonnegative
power of `f`. The ambient scheme is compact and quasi-separated. The bundle
itself is unchanged.

The proof uses local rank-one trivializations and the coordinate maps
`SectionClearing.chartE` and `chartF`. Choose a finite cover by affine opens
contained in those trivializations. Affine localization of regular functions
extends the coordinate of the local section after a power of `f`. Increase
the finitely many exponents to one common exponent. On each overlap the
difference of two lifts vanishes after restriction to `D(f)`. The overlap is
compact by quasi-separatedness, so scalar denominator clearing kills the
difference by another power of `f`. Choose a common power for all overlaps
and glue using the actual sheaf condition.

This is derived infrastructure for the finite-section theorem. Its proof
adapts the finite-chart gluing argument in `LineBundleSectionClearingProof`,
with arbitrary local line-bundle sections in place of scalar multiples of
already global sections. The algebraic inputs and chart comparisons are
published Library and Mathlib results. It assumes no Noetherianity,
reducedness, integrality or field structure.

The public definition `PrincipalSectionExtension.extension` chooses an exponent
and an extending global section and returns them with the restriction equality
as a subtype certificate. Its existence is provided by the theorem
`exists_global` described above. This is a noncomputable choice; no uniqueness
or minimality of the exponent is asserted.
