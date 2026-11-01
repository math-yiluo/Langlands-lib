# Second-block corank coefficient specialization

Worker 486. This internal composition applies the second-block deformation
interface at induced rank `r + 2`, then applies the corank entire-slice theorem
to the actual resulting coefficients for the supplied quotient measure.

`corankCoefficientSeries F ψ ν U Wprime` is the unrestricted integer-indexed
series of determinant-slice integrals of
`corankOneIntegrand ψ (normalizedAbsoluteValue T) U Wprime 0`, where
`T = F.canonicalTopologicalData`. It is the same coefficient formula as
`corankCoefficientFamily` at one fixed parameter, now named independently of
any parameterized family. Its definition asserts no convergence or support.

`SecondBlockCorankRealRayClearing` is an explicit proposition, not an asserted
analytic theorem. For every real `u > C`, every nonzero standard Whittaker
functional of the literal second-block deformed lower induction, and every
vector of its actual carrier, it requires a Laurent polynomial whose embedded
series equals the actual coefficient series multiplied by

```text
(P0 * P1.comp (Polynomial.C (spectralPoint q u) * Polynomial.X)).toLaurent,
q = T.residueCardinality.
```

The initial block order, dependent carriers, and representations are retained.
Only the second lower block is deformed. The existential Laurent polynomial
may depend on `u`, the functional, and the vector. No uniform support bound
for these outputs is a premise.

`secondBlock_entireCorankFamily` retains the closed second-block deformation
proposition as `hdeform`. The input is any nonzero standard functional at
parameter zero and any vector `W0` in its actual coefficient image. Applying
`secondBlock_whittakerFamily` at `t = r + 1` supplies a family `U` with the exact
identity `U 0 = W0.val`, actual nonzero functional/vector realizations at every
parameter, one compact open right level, and pointwise analyticity. Applying
`corankCoefficientFamily_integrable_entire` to this same family proves slice
integrability at every parameter and entire dependence of each literal
coefficient. The inverse-character test representation may be reducible of
full Whittaker type, and its functional and coefficient may be zero. The
field, test carrier, and dependent block carrier universes are independent.
The original supplied compatible quotient measure is used throughout.

`secondBlock_corankClearing_at_zero` adds the explicit
`SecondBlockCorankRealRayClearing` premise for the fixed inverse coefficient.
For each large real parameter, the preceding family's actual realization
supplies the functional and vector to that premise. Substitution of their
coefficient-map equality gives formal clearing for the same entire family.
The proved Laurent-kernel specialization then supplies clearing at zero.
Rewriting `U 0 = W0.val` yields the literal original coefficient series, cleared
by `(P0 * P1).toLaurent`. The proof never cancels a Laurent polynomial in the
bilateral series module.

This is an internal consequence of the imported interfaces; it adds no direct
literature claim. Their source motivation is the coefficient continuation
argument of JPSS (1983), Section 4.5, printed pages 408–410, and the positive
second-block parameter of Section 6.1, printed page 427. Both `hdeform` and the
formal real-ray clearing proposition remain explicit. Neither a rational
integral identity nor a denominator-span bound is silently treated as a formal
coefficient equality. No gamma factor, L-polynomial certificate, block reversal,
or closed adjacent-rank base proposition is proved here.
