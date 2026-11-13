# The spin-kernel comparison from an adapted orthogonal chart

This internal assembly connects an all-test compatibility property of full orthogonal coordinates with the original binary spin cocharacter. The coordinate compatibility remains an explicit hypothesis. The module is derived from the published spin-kernel reductions and the split cocharacter construction.

`doubleCoordinateCocharacter` is the inverse image of the integral coordinate vector \(2e_{i_0}\) under the split-torus cocharacter equivalence. The coordinate lemma identifies it under `GeneralLinear.cocharacterCoordEquiv`. Its point lemma sends a unit \(t\) to the family with \(t^2\) at \(i_0\) and \(1\) elsewhere on every relative test scheme.

`IsAdaptedOrthogonalCoordinates` specifies the needed property of a full orthogonal group-scheme isomorphism after extension to a quaternion splitting field: an original hyperbolic Levi element with chart \(\operatorname{diag}(s,1)\) becomes the orthogonal coordinate diagonal with entries \(s,s^{-1}\) in the selected hyperbolic pair.

`splitSpinCocharacter_comp_eq_diagonal` uses this property, the all-test ambient action of the split spin cocharacter, and the chart formula \(\operatorname{diag}(t^2,1)\). Equality on every test gives equality of group-scheme morphisms.

`kernelGenerator_of_adaptedCoordinates` then applies `kernelGenerator_of_orthogonalCoordinates`, with the square-root comparison already proved for the original binary diagonal. It assumes at least three orthogonal hyperbolic coordinates and retains all hypotheses of the original spin construction, including the explicit degree-two norm-one simple-connectedness proposition.
