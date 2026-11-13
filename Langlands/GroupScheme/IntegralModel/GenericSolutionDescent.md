# Generic comparisons for effective integral group descent

This internal construction descends a compatible generic comparison of an
actual affine fpqc solution. It supplies a structural step toward integral
unramified model descent. It does not construct descent data from stable
integral points.

## Scope and inputs

The rings, fraction fields, coefficient square, original generic group `G`,
upstairs smooth integral model `N`, actual datum `D` and affine solution `s`
have the same meaning as in `AffineDatumDescent`. All types lie in an arbitrary
universe `u`.

`solutionModel s hN` regards the solution group as a smooth model of its own
actual generic fibre, with identity generic identification. Its coefficient
comparison, the generic fibre of `s.iso`, and `N.genericIso` give
`solutionGenericComparison s hN`, an isomorphism over `L` from the scalar
extension of the solution's generic fibre to `G_L`.

## Construction and proof

`isoOfSolutionGenericRecovery` proves that any generic isomorphism over `K`
recovering this comparison gives the exact compatibility equation needed by
`isoOfAffineSolution`. The proof cancels the coefficient comparison and uses
the definition of `baseChangeGenericIso`.

`SolutionGenericCompatible` asserts actual Čech compatibility of the comparison
with the two canonical data for `Spec L → Spec K`. This is an explicit input.
The fraction-field extension is faithfully flat and quasi-compact.
`solutionGenericIso` applies the published `Solution.descendIso` to the two
canonical solutions. `baseChange_solutionGenericIso` records its exact
recovery.

`ofGenericCompatibleSolution` uses that descended isomorphism as its generic
identification. Its smoothness follows from the published affine-solution
construction. `isoOfGenericCompatibleSolution` uses exact recovery to provide
an isomorphism from its coefficient extension to `N` over the identity of
`G_L`. The underlying group isomorphism is the given `s.iso`.

## Provenance and remaining obligations

These are internal consequences of actual fpqc morphism descent and the
integral-model coefficient APIs. There is no additional source theorem claimed.
For KP Fact 2.10.16, the actual datum and compatibility of the generic
comparison must still be proved from Galois-stability of the integral-point
image.
