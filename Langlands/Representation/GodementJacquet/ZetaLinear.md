# Linear closure of actual matrix zeta integrals

This module supplies internal linear algebra and integration infrastructure for
the analytic induction argument. It uses the actual full-matrix integrand,
Bochner integral, shifted rational-value relation and bi-smooth coefficient
submodule from `Zeta`. It does not prove a noncompact integration formula or
analytic induction.

The matrix integrand is linear in its coefficient function. Integrable functions
are closed under addition and complex scalar multiplication, giving
`matrixConvergenceSubmodule` for any fixed test and spectral parameter. Its span
property proves `matrixConverges_of_mem_span`. The integral is additive when both
integrands are integrable, and commutes with constant scalar multiplication.
No additivity assertion is made outside the integrable domain.

The zero function has shifted rational value zero. Addition of two actual
shifted rational values uses the intersection of their convergence half-planes,
the actual additive integral identity there, and the published rational
continuation addition and transfer lemmas. Constant multiples use the actual
scalar integral identity and the published constant-multiple continuation
lemma, including zero scalars. These continuation lemmas preserve reduced
denominator nonvanishing on a right half-plane.

For a prescribed Laurent submodule `W`, `matrixRationalCoefficientSubmodule`
consists of coefficient functions admitting an actual shifted rational value in
`W`. Addition stays in `W`; a complex scalar acts through the corresponding
constant Laurent polynomial. Thus rational-value existence and membership in
`W` extend to the whole complex span of any set of coefficient functions.

`matrixConvergesOnRight_iff_generators` specializes integrability closure to the
published bi-smooth coefficient space. The bound is chosen before all tests,
smooth functionals, smooth vectors and spectral parameters, and the same bound
works for the entire coefficient span. It does not replace this uniform bound
with a separate bound for each coefficient.

`exists_hasShiftedRationalValue_mem_of_generators` similarly extends rationality
and membership in `W` from individual smooth coefficients to the whole
bi-smooth span. When `q > 1`,
`zetaSpan_matrixRationalValues_le_of_generators` also puts every rational value
in the published Laurent span inside `W`: uniqueness of rational continuation
identifies any given value with the one supplied by linear closure. This step
retains the denominator guards instead of selecting or identifying totalized
values at poles.

All results allow arbitrary topological fields, arbitrary group measures, smooth
parts of arbitrary complex representations and independent field and carrier
universes. Smoothness of the entire representation, admissibility,
irreducibility, a central character and a Fourier measure are unnecessary for
these linear closure arguments. The provenance is the definitions of the
actual matrix integral, linearity of the Bochner integral and the published
algebraic rational-continuation lemmas.
