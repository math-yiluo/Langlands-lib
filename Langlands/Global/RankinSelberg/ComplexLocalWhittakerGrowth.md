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
