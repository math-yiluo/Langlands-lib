# Cleared corank coefficients and rational denominator bounds

Worker 486. This internal consumer converts formal Laurent clearing of actual
corank coefficients into the reciprocal-polynomial denominator bound. Its
scalar argument applies to unrestricted bilateral series.

`HasBilateralSpectralExpansion q a f` requires a real bound `C` such that
the integer-indexed series `a m * spectralPoint q s ^ m` has sum `f s` at
every complex `s` with `C < s.re`. It includes convergence of these actual
sums. It imposes no exponent support condition.

`clearedSpectralExpansion_rationalIdentity` takes this expansion, a rational
continuation `R` of `f`, and formal equality of the embedded coefficients of a
Laurent polynomial `Q` with `P.toLaurent • a`. It proves

```text
laurentToRatFunc Q = algebraMap (Polynomial Complex) RationalFunctions P * R.
```

For each parameter in the convergence half-plane, the proved finite Laurent
action evaluation gives a sum for `P.toLaurent • a`. The embedded polynomial's
finite sum has the same terms by the formal equality. Uniqueness of scalar
sums gives `laurentEval x Q = P.eval x * f s`, where `x` is the nonzero
spectral point as a unit. The published Laurent evaluation theorem proves
the rational image of `Q` is regular there, so this identity supplies an
actual rational continuation of the scalar product. The polynomial factor
itself has its obvious everywhere regular rational continuation. The proved
product transport gives the continuation `algebraMap P * R` of the same
scalar function. Published rational-continuation uniqueness, based on the
infinite set of real spectral points when `q > 1`, identifies these two
rational functions. No coefficient-uniqueness or formal-series cancellation
is used in this direction, and `P` may be zero for this identity.

`clearedSpectralExpansion_mem_reciprocalSpan` assumes additionally `P ≠ 0`
and an existential `Q`. The preceding identity gives
`R = laurentToRatFunc Q * (algebraMap P)⁻¹`, now by multiplication in the
field of rational functions. The singleton-span criterion proves membership
in the Laurent span of that reciprocal.

`Padic.corankClearing_denominatorBound` applies this result to the literal
determinant-slice coefficients at spectral parameter zero and the same
supplied quotient measure `ν`. It retains convergence of the original
corank integrals on a right half-plane as an explicit premise. The published
`corankOneSliceExpansion` supplies the actual spectral sums there. The
conclusion is exactly `AdjacentRankCorankDenominatorBound` for the specified
Whittaker functions: every rational continuation of that integral belongs
to the reciprocal Laurent span. Existence of a rational continuation is
neither required nor asserted by this lemma.

`Padic.corankOneCoefficient_clearing_denominatorBound` discharges the
half-plane convergence premise for vectors in actual nonzero functional
images of two full Whittaker-type representations, using the published
`corankOneCoefficient_convergesOnRight`. That theorem in turn consumes the
closed unequal-rank analytic theorem at the zero-row block. The complete
representations may be reducible, either coefficient may be zero, and the
two carrier universes are independent of each other and of the field. The
quotient measure is the supplied compatible measure; an arbitrary additive
Haar measure is supplied to the zero-row analytic theorem. Self-duality is
not required for convergence.

The provenance is internal composition of published spectral expansion,
Laurent evaluation, rational continuation transport and uniqueness. The
module adds no direct literature assertion. Formal clearing remains an
explicit input: a denominator bound or rational evaluation equality is
not treated as coefficient equality. No analytic deformation, gamma factor,
L-polynomial certificate, block reversal or exact adjacent-rank base target
is proved here.
