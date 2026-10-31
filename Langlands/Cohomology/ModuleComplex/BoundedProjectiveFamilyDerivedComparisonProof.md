# Converting raw projective families to derived comparisons

`Langlands.Cohomology.ModuleComplex.boundedProjectiveFamilyDerivedComparison.{u}`
proves the matching `BoundedProjectiveFamilyDerivedComparisonStatement`.
Its input is a commutative ring R and a bounded natural-number family K
of finite projective R-modules with square-zero linear differentials δ.
It uses no noetherian hypothesis.

The proof assembles K and δ using `CochainComplex.of` and chooses its
extension by zero to the integers as P. The published
`boundedNatComplexExtension` proves that P is strictly perfect. This
choice precedes every target family, target map and scalar extension.

For the original base, the supplied R-module family C and differential d
are assembled in the same way. The differential-commutation hypothesis
turns φ into a genuine complex morphism. The four assumed cycle and
boundary tests are precisely the inputs of the published
`natModuleQuasiIsoCriterion`, so this morphism is a quasi-isomorphism.
Extension by zero preserves it, and its image under the standard
derived localization Q is invertible. The associated isomorphism is
the required original-base comparison.

For A and f : R → A, the proof installs `f.toAlgebra` and uses the actual
`ModuleCat.extendScalars f` functor. Its image of the natural-number K
complex has modules A tensor K and the differentials `(δ i).baseChange A`.
The maps Θ, with the assumed differential identity and the four scalar
cycle and boundary tests, therefore give another categorical
quasi-isomorphism, to the assembled A-module target C. Its extension
and localization supply the second comparison. The inverse of
`DerivedPlus.mapExtendIso`, mapped through Q, first identifies the
ordinary scalar extension of the already chosen integer complex with
the integer extension of the scalar natural-number complex.

Target families C need not be bounded, flat or finite. Neither the
original-base nor scalar clause proves its assumed elementwise tests;
both convert supplied tests to actual derived isomorphisms. No geometric
Čech comparison, right-derived sections comparison, or compatibility of
the chosen isomorphisms is claimed.

## Provenance

This is an internal assembly of the published extension and
quasi-isomorphism criterion, plus the existing comparison for extension
and functors. Workers 137 and 958 designed the raw-family interface;
Worker 137 implemented the proof. It isolates the conversion needed by
the geometric construction while importing no unpublished port files.
