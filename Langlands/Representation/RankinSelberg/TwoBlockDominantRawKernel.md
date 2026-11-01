# Actual raw scalar kernels for JPSS Section 4.10

The source is Jacquet–Piatetski-Shapiro–Shalika (1983), Section 4.10(2),
printed page 419, registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source formula supplies the actual matrix and exponent. The residual
calculation and the rectangle coordinate change are internally derived
support for covariance. Worker 484 supplied that mathematical design;
Worker 1209 constructed the actual matrices and proved their covariance;
Worker 1198 implemented the residual character and these scalar kernels.

Let `m : Fin 2 → ℕ`, `a=m 0+1`, `b=m 1+1`, `c=j+k+1`,
`a+b=t+1`, and `r=t+c`. The rectangle sizes are `a×k` and `j×b`, with
arbitrary natural `j,k`, including zero. The field is any
`F : PadicField.{uF} p` with `p` prime. Both the character and block inverse
Whittaker functionals use `F.canonicalTopologicalData.topology`. The two
complex representation carriers live in an independent universe `uW`.
All actual block representations `σ`, all inverse functionals `ell`
including zero, all sections `f : TwoBlockJacquet.Sections F h σ`, and
all actual `Wtest : WhittakerFunctions ψ r` are allowed.

`rawScalarValue ell f Wtest g P` is the product
`scalarSection (fun i => (ell i).val) f g 1 * Wtest.val P`,
on actual general linear group representatives. `rawKernel` evaluates `P`
at the constructed `matrix h hr g x y`. The weighted `kernel`, for every
complex `s`, multiplies this value by

```text
determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
  g (s - (c : ℂ)/2 + (j : ℂ)).
```

`kernel_eq` exposes the complete product on the actual section, coefficient
and five-block matrix.

`determinantWeight_lowerBlockUnipotent_mul` proves that left translation
by the actual lower-block unipotent leaves the determinant weight unchanged
for every complex exponent. The proof applies the published determinant-one
law of that subgroup and determinant multiplicativity.

The private scalar cancellation lemma combines the published actual
`scalarSection_lowerBlockUnipotent_mul` law, whose multiplier is the inverse
product character, with the Whittaker coefficient's positive character.
It cancels the two pairs of inverse units in `ℂ`. The next private lemma
supplies the actual `residualUnipotent` and its proved character, so that
this cancellation requires no character law from the caller.

`rawKernel_covariance` rewrites the actual matrix of `u*g` by the imported
`matrix_covariance`, then uses this computed-residual cancellation. Thus
the two simultaneous transformed rectangles are

```text
x' = LA⁻¹*x,     y' = y*LB,
LA = w_a*uA*w_a, LB = w_b*uB*w_b.
```

They are the projections of the constructed linear equivalence
`rectangleChange h j k u (x,y)`. No matrix or character identity is a
hypothesis of this theorem. `kernel_covariance` combines it with
determinant-weight invariance to give, for every complex `s`,

```text
kernel ell f Wtest hr s (u.val*g) x y =
  kernel ell f Wtest hr s g x' y'.
```

Both laws retain arbitrary complementary dimensions, the independent field
and representation-carrier universes, all representations, and all inverse
functionals including zero. They have no irreducibility or nonvanishing
premise.

These are representative-level scalar data. The simultaneous rectangle
change is part of the law; fixed-rectangle quotient invariance is not
asserted. There is no quotient integral, rectangle-Haar preservation,
integrability, convergence, Fubini, Laurent identity, reversed-dual analytic
comparison, factor existence or dominant-rank base proposition here.
