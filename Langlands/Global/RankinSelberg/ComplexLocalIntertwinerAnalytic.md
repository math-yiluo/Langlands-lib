# Real analyticity of smooth images of complex principal series vectors

`ComplexLocalIntertwinerAnalyticStatement` assumes a complex-linear map
sends unitary-finite standard module vectors to smooth functions and
commutes with the action of every real Lie generator. Its image functions
are real analytic in the invertible matrix chart.

The coordinate square action becomes the Hessian sum in that chart. The
first-order terms from a matrix unit and its imaginary multiple cancel.
Decompose the inducing vector into finitely many square-operator
eigenvectors. Each image solves a scalar elliptic eigenfunction equation,
so scalar analytic regularity and the finite sum give analyticity.

`analyticOnNhd_unitsExtension_complexWhittaker` applies the criterion to the
Library's Whittaker intertwiners. The criterion also applies to a compact
average of an intertwiner's values once the corresponding differentiation
identity is supplied. Its intended use is the compatibility of the
Whittaker map with compact averaging in Jacquet's §4.7 argument.
