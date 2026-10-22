# Left translation and the manifold formula for smooth differentiation

This module supplements the published genuine smooth differential for every
number field and every natural matrix rank, including zero.

`smoothLeftTranslation K n a` is the complex-linear pullback operator
\(f(x)\mapsto f(ax)\) on the actual completion-coordinate smooth-function
space. Its defining proof transports multiplication to the mixed-coordinate
Lie group and composes its smooth left-multiplication map with the given
smooth function. Its linearity follows pointwise. The theorem
`smoothLeftTranslation_apply` gives its evaluation formula.

`smoothDifferential_eq_mfderiv` identifies the published ambient-coordinate
differential with the actual real manifold derivative of
\(h\mapsto f(c^{-1}(h))\) at \(c(x)\), applied to \(c(x)X\), where \(c\) is
`archimedeanGLCoordinates`. The output tangent space of the normed space
\(\mathbb C\) is canonically identified with \(\mathbb C\) by
`NormedSpace.fromTangentSpace`. The source vector uses the units chart,
whose map is the inclusion into the ambient matrix algebra.

The proof unfolds the manifold derivative in that chart. The chart expression
is precisely the published `coordinateExtension`; the real model has full
range, so the derivative within the model range is the ordinary derivative.

These are derived implementation constructions for the real Lie-group
differential and left-invariance framework of Borel–Jacquet, *Automorphic
forms and automorphic representations*, section 1.1, printed page 189
(one-based PDF page 184), and section 4.1, printed page 194 (PDF page 189).
The registered source is `borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The exact implementation formulas are derived rather than quoted.
Commutation of differentiation with left translation and the Lie bracket
law are separate proof obligations.
