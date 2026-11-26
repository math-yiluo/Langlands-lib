# Extension from an arithmetic slice

Let `L` be an open subgroup of the finite adelic group. The rational
stabilizer of the coset `b L` consists of the rational points `q` with
`b⁻¹ * r_f(q) * b ∈ L`. Its infinite projection acts on the infinite
points by left multiplication. The submodule `arithmeticSliceFunctions`
consists of the plot-smooth functions invariant under this action.
Given such a function, `extendArithmeticPlotSmoothSlices`
assigns zero to every finite slice outside the rational orbit of `b L`.
If the finite component can be written `r_f(q) b l` with `l ∈ L`, the assigned
slice is the pullback of the original function by multiplication on the
left by `r_∞(q)⁻¹`. Two choices differ by a rational element whose finite
projection is in `b L b⁻¹`. Invariance under its infinite projection proves
independence of that choice. Multiplication on either side of the finite
component verifies rational covariance and right-level invariance.

The reconstruction `reconstructFinitePlotSmoothSlices` uses
`SmoothOfRelativeDimension d G.X.hom` to obtain continuity of the original
plot-smooth slices and turns this family into an actual finite plot-smooth
function on the rational quotient.
The extended function is right invariant under the original level `L`.
Each of its slices is zero or a left translate of the input. The identity
rational point can be used at `b`, so restriction at `b` recovers the
original function. This proves injectivity of the linear extension map
`extendArithmeticPlotSmooth`.

This construction implements extension from one summand of the arithmetic
quotient decomposition in Borel–Jacquet, *Automorphic forms and automorphic
representations* (1979), §4.3 (1)–(2), printed p. 195, PDF p. 190 of
`borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
