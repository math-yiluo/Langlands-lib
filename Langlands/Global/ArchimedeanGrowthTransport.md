# Polynomial growth under arithmetic archimedean transport

Author: Worker 2.

For actual number fields in independent universes and every natural matrix
rank, including zero, this internal construction proves preservation and
reflection of the existing matrix-height polynomial-growth condition under
arithmetic pullback. The values are complex numbers and are unchanged by
the arithmetic map. The actual infinite matrix groups retain their completion
topologies and mixed real/complex coordinates.

`growthBound n e` is the maximum of one and the real operator norm of the
existing `matrixRealLinearEquiv n e`. It is at least one.
`coordinates_arithmetic_map_apply` identifies the actual arithmetic matrix
map in the existing coordinates. The continuous real-linear operator estimate
bounds the norm of its matrix value by `growthBound` times the old matrix
height. Applying the same estimate to the inverse controls the inverse matrix.
Consequently `matrixHeight_arithmetic_map_le` proves

```
height_L (arithmeticMap e g) ≤ growthBound n e * height_K g.
```

If a function has growth constant `C ≥ 0` and natural exponent `d`, its
pullback has constant `C * growthBound n e ^ d` and the same exponent.
The inverse arithmetic map gives the converse; it is not necessary that the
displayed bound be sharp or the two heights be equal.

`polynomialGrowthComap` constructs complex-linear pullback on the existing
polynomial-growth submodules. Evaluation is actual arithmetic substitution.
Identity and contravariant composition follow from the actual arithmetic
ring laws. `polynomialGrowthEquiv` uses pullback along the inverse field
isomorphism as a genuine two-sided inverse. Its forward and inverse evaluation
formulas are stated explicitly. `smoothComap_hasPolynomialGrowth_iff`
also gives the condition for the existing actual smooth pullback.

Provenance is internal: this combines `ArchimedeanGLTransport`'s continuous
real-linear arithmetic matrix model, `ArchimedeanGrowth`'s specified matrix
and inverse height, and the operator-norm inequality for continuous linear
maps. It changes no growth or normalization convention and cites no new
literature identification. It does not assert continuity for a derivative
topology or preserve enveloping-center finiteness, cuspidality, or automorphic
occurrence.
