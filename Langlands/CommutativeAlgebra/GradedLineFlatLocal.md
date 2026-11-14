# Flat graded lines over an arbitrary local ring

This internal extension of `GradedLineLocal` replaces reducedness of the
local base by flatness of the graded algebra.
`exists_aeval_bijective_of_flat` concerns a finite type algebra `A` over a
commutative local ring `R`, equipped with the published `IsGrading` coaction,
with no negative components and scalar degree-zero component.
It assumes a graded map from `A` to the polynomial ring over the closed
residue field, with the variable in a positive degree `d`, whose span
contains that variable and whose kernel is contained in the extension of
the maximal ideal. It proves that evaluation at a homogeneous element of
degree `d` is a bijection from `R[X]` to `A`.
No reducedness or noetherian hypothesis is imposed.

The implemented proof reuses the finite generation of homogeneous
components and the graded Nakayama argument in `GradedLineLocal` to
choose a homogeneous generator `x` whose powers span the corresponding
components. Each component is a retract of the flat algebra, so is flat.
It is finite and hence free over the local ring. The image of every power
of `x` in the closed fibre is nonzero, so each such component is nonzero.
A nonzero free module is faithful. Since its indicated power generates
it, no nonzero scalar annihilates that power. Applying the homogeneous
projections to a polynomial relation in `x` now shows that every
coefficient is zero, including coefficients in nilpotent ideals.
The existing graded Nakayama argument also gives surjectivity.

`flat_homog`, `powSpan_mul_eq_span` and `comp_aeval` record the retract,
single-generator and coefficient-projection steps.
`exists_aeval_bijective_of_flat_of_universal` packages the same result
using the published universal-line condition over the closed residue
field. `polynomialEquivOfFlatOfUniversal` chooses the resulting homogeneous
coordinate and packages evaluation as an `R`-algebra equivalence
`R[X] ≃ₐ[R] A`; the choice is not canonical.
This is a consequence of the existing grading interfaces and
Mathlib's finite flat module freeness over a local ring; no new external
classification result is used.
