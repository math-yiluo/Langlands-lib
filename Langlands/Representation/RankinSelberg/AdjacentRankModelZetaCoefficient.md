# Actual adjacent-rank model coefficients

This module implements the substitution and finite coefficient calculation at
the start of JPSS Section 6.3, printed pages 432–435, formulas (1), (3)–(10),
using the existing literal adjacent-rank model integral. The registered original
is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 486 read printed pages 404–405 and 427–439 and reread pages 432–435 for
these model and coefficient computations. The bounded registered-source and
correction-note audit found no JPSS-specific registered erratum.

The group in the inner integral has actual rank `r+1`, and the model has ambient
rank `r+2`. The field topology, valuation, local-field structures, Hausdorffness,
second countability and sigma compactness are the canonical structures of the
supplied p-adic field. The representation universes are independent of one
another and the field universe. All natural `r`, including actual inner rank
one, and reducible representations are retained.

## Separated test and exact substitution

`adjacentRankSeparatedTest` is the rectangular Schwartz–Bruhat function
`[x,y] ↦ Φ(x) φ(y)`. It pulls the external product back through the published
rectangular splitting homeomorphism. Its join evaluation is proved explicitly.
The elementary Fourier covariance already proved in
`PartialFourierCovarianceProof` evaluates its `rho0(diag(g,1))` transform at the
square block `h g` and the last row of `h⁻¹`. This uses the supplied self-dual
additive Haar measure without altering it.

Writing `a(h) = χ(det h) |det h|^(r/2)`,
`adjacentRankModelIntegral_separated_rankInclusion_raw` is the literal formula

```text
M(diag(g,1)) = χ(det g) |det g|^((r+1)/2)
  ∫ Φ(h g) φ(lastRow(h⁻¹)) W(h⁻¹) a(h) dh.
```

The square test is evaluated on the underlying matrix. The integral uses the
existing GL Haar measure normalized by mass one on integral points.
`adjacentRankInnerMultiplier_mul` proves the multiplicativity needed for the
change of variables, including the determinant character and complex power.

`adjacentRankModelIntegral_separated_rankInclusion_weighted` proves, for every
complex `s`,

```text
M(diag(g,1)) |det g|^(s-1/2) = |det g|^s
  ∫ Φ(h) φ(lastRow(g h⁻¹)) W(g h⁻¹) a(h) dh.
```

The implemented proof uses right translation `h ↦ h g` in the same Haar
measure, whose right invariance is already published. If `orig` and `after`
denote the two integrands, `after(h g) = a(g) orig(h)` pointwise. Right
invariance and scalar linearity give the corresponding integral equality.
The existing exponent-addition law then identifies
`(r+1)/2 + (s-1/2) = s+r/2`. These raw identities hold for totalized Bochner
integrals; they assert no convergence by themselves and require no image theorem.

## Actual determinant coefficients

`adjacentRankModel_corankOneSlice_eq_before` takes a Whittaker function `U`
and an explicit equality identifying its whole underlying function with this
separated pure-tensor model. For any inverse-character Whittaker function `W'`,
it identifies the indicator of the actual corank-one integrand at `s=0` on
slice `m` with the inner integral of `adjacentRankBeforeShearKernel`. The proof
passes to a quotient representative, uses the weighted substitution at zero,
and inserts `W'(g)` by scalar linearity. On the complement of the slice both
expressions vanish. The equality does not construct `U` or prove image membership.

`adjacentRankModel_corankOne_finiteConvolution` adds smoothness of the first
representation and admissibility of a second representation at character
`ψ.scale(-1)`. It preserves any supplied quotient measure compatible with the
same GL and upper-unipotent Haar measures. It chooses lower determinant bounds
`Lq,Lh` and a finite family `B` in the second representation's actual Whittaker
coefficient image before the second vector `W'`. It then chooses bi-smooth
matrix coefficients `f_i` before all total shell orders `m`. The published
`scaledStandardAsInverse` adapter preserves the underlying functions.
With that adapter understood, the actual coefficient is

```text
sliceCoefficient(corankOneIntegrand(U,W',0), m)
 = ∑ k ∈ [Lq, m-Lh], ∑ i,
     equalRankSliceCoefficient(W,B_i,φ,k)
       * ∫ adjacentRankInnerSliceWeight(Φ,χ,m-k,r/2,h) f_i(h) dh.
```

The theorem also proves convergence on every determinant slice of the corank-one
integrand and integrability of every equal-rank slice factor and group integral
in this formula. It reuses `adjacentRankShell_finiteConvolution`, which already
establishes both joint kernel integrabilities and the finite convolution. The
new pointwise slice equality transfers its iterated integral to the actual
corank-one coefficient. Integrability of the inner-integral function follows
from the genuinely integrable product kernel; the measurable slice indicator
then gives genuine integrability on each determinant slice. Thus the coefficient
identity is accompanied by convergence and does not rely on a divergent integral
being totalized to zero.

This is a derived prerequisite for the parent adjacent-rank task. Whittaker image
and spanning, the global Laurent-series identity, half-plane summability,
functional equations, lower-to-upper induction comparison and both exact parent
gamma/L factor certificates remain separate obligations. In particular the
explicit realization equality is not a premise added to either parent theorem.
The finite convolution dependency and its joint-shell and quotient-shear helpers
retain their own separate review and publication steps.
