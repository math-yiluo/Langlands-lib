# Uniform derivative growth for complex local Whittaker functions

`ComplexWhittakerUniformDerivativeGrowthStatement` gives one nonnegative integer
exponent for each vector of the published complex local Whittaker model. For
every finite word in real right Lie derivatives, the resulting function is
bounded by a nonnegative constant times that power of
`max 1 (complexMatrixHeight g)`. The constant can depend on the word, including
its matrix directions. The empty word gives the original function.

The proof uses a complex place of the number field obtained by adjoining
`Complex.I` to `ℚ`. Evaluation at the chosen place projects the archimedean
matrix group to the complex matrix group. Its section inserts a group element
at that place and identities at the other places. Pullback preserves
smoothness by the matrix chart on the open set of units. The chain rule
transports real right derivatives through the projected direction, and
iteration transports every finite word.

For each generating intertwiner of the model, the pullback intertwines the
compact action with the action of its unitary projection, so the compact
orbit spans a finite-dimensional space. The same pullback intertwines the
enveloping action via the complexified Lie projection. The enveloping
projection is surjective, so it sends central elements to central elements.
The infinitesimal character of the complex standard module then puts the
central orbit of each lifted image vector in a line. Compact finiteness and
center finiteness are submodule conditions, which extends both to the
pullback of the entire Whittaker model.

For rank \(n\), the clamped complex height of a projection is at most
\((1+2n^2)\) times the square of the archimedean height. The archimedean
height of a section value is at most \((1+n)\) times the clamped complex
height. Hence a vector's original complex exponent \(d\) gives exponent
\(2d\) on the archimedean group. `finiteUniformDifferentialGrowth` preserves
that exponent under every enveloping derivative, and restriction to the
section returns the desired complex bound with exponent \(2d\).

This is an internal version of the derivative-growth input to Jacquet's
majorization argument in §3.2, pp. 15–16, especially the bound preceding
(3.11). Jacquet obtains that input using continuous seminorms on his
representation space. The proof here uses the fixed-exponent growth
theorem on the pullback of each vector in the Library model. The proposition
supplies the common exponent for that vector's derivative words. The
simple-root majorant of Proposition 3.1 and convergence of the local
integrals require further estimates.

## Uniqueness from evaluation at the identity

`complexWhittakerEvaluation` proves that two exact complex Whittaker intertwiners agreeing at the identity on every compact-finite standard vector are equal. It reuses the complex-place lift and its compact and central finiteness from the uniform growth proof. The two group coefficients are lifted to the archimedean group of the same number field. Both lifts have finite joint orbits under the center and the compact enveloping algebra, so the difference is real analytic in matrix coordinates.

For any group point, choose a compact representative of the component containing its lift. Every enveloping derivative of the difference at this representative is the difference of the two identity evaluations on a compact translate of the same projected enveloping derivative of the input vector. These values vanish by the evaluation hypothesis. The enveloping zero-jet theorem gives a zero matrix jet, and analytic uniqueness propagates this equality to the lifted point. Projection composed with inclusion recovers the original complex point. Specializing the auxiliary field to the complex place of the Gaussian rationals proves the assertion for the given complex module.

The result identifies the coefficient map from its scalar evaluation functional. Classifying the possible evaluation functionals remains a separate step.

## Compatibility of compact projection with the Whittaker map

`ComplexLocalWhittakerGrowth.complexWhittakerCompactProjection` takes an exact Whittaker intertwiner, a standard vector, a group translate, and a continuous compact weight with finite left translate span. It produces a compact-finite standard vector whose values are the weighted compact average of the translate, and whose Whittaker values are the same weighted compact average of the translated Whittaker value.

Lift the standard vector and the Whittaker value to a pair of smooth functions on the archimedean group. The image of this pair map is stable under the simultaneous compact and enveloping operations, because their projections to the complex place act on the original standard vector. The infinitesimal character and the finite compact orbit of that vector make each coordinate joint finite. A compact average takes this pair space into itself by finite compact orbit closure. The average has finite-dimensional image there. Indeed restriction of the first coordinate to the local unitary group is injective on pairs by the compact description of the principal series. Left invariance of Haar measure writes the projected compact values as integrals with the left-translated weight. Its finite translate span gives a fixed finite sum of separated functions, hence a fixed finite-dimensional space containing those compact restrictions.

The simultaneous translation theorem puts the projected translate in the image of the original pair map. Evaluating the two coordinates of this membership gives the inducing-vector and Whittaker formulas with the given compact Haar measure. The proofs of this theorem and of identity-evaluation injectivity both reuse the exact complex-place pullback from the growth argument above.
