# Adjacent-rank spectral expansion

This derived prerequisite supplies the spectral expansions needed to pass from
the finite determinant-coefficient formula in JPSS Section 6.3, (9), to the
integral identity (10), printed pages 435–436. It proves an integer Cauchy-product
adapter and the expansions of the actual corank-one and shifted matrix integrals
at parameters where their integrands are integrable. It does not prove a common
half-plane of convergence or the finite sum of products.

The registered source is **jpss-1983-rankin-selberg**, Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983), SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Theorem 3.1, printed pages 404–405, and Section 6 through the case enumeration
in Section 7.1, printed pages 427–439, were read for the surrounding proof.
This module uses only the coefficient-to-series step on pages 435–436.
The bounded registered-errata checks recorded in the worker's source reading
found no JPSS-specific erratum.

## Integer Cauchy product

`hasSum_intervalConvolution` takes two scalar sequences `a,b : ℤ → ℂ`,
lower support bounds `La,Lb`, a nonzero complex `z`, and sums
`HasSum (a(k) z^k) A` and `HasSum (b(k) z^k) B`. It proves both absolute
summability and

`HasSum ((∑ k ∈ Icc La (m-Lb), a(k)b(m-k)) z^m) (A B)`.

Empty intervals are allowed. The proof uses the equivalence between summability
and absolute summability in finite-dimensional complex space, the absolutely
convergent product indexed by `ℤ × ℤ`, and the bijection
`(m,k) ↦ (k,m-k)`. Each fiber vanishes outside the stated finite interval.
The identity `z^k z^(m-k) = z^m` then gives the finite coefficient expression.
This does not multiply unrestricted bilateral Laurent series.

## Canonical field and actual integrals

The remaining declarations use every canonical p-adic field `F`, all natural
`r`, the canonical topology and normalized absolute value, and the existing
residue cardinality `q`. The group has actual rank `r+1`, including rank one.
Write `z = spectralPoint q s = q^(-s)`.

`adjacentRankMatrixSliceCoefficient F Φ χ f m` is the literal scalar integral

`b(m) = ∫ h, 1_{ord(det h)=m} Φ(h) χ(det h) |det h|^(r/2) f(h) dh`.

Here `Φ` is a Schwartz–Bruhat function on the full square-matrix space, `χ` is
a quasicharacter, `f` is any complex-valued group function, and `dh` is the
existing `generalLinearHaar`. This definition reuses
`adjacentRankInnerSliceWeight`; it adds no new measure normalization or
representation condition.

`hasSum_setIntegral_generalLinearDeterminantSlice` proves the integral
partition for any Borel measure on this general linear group and any integrable
complex function. The determinant-order fibers are measurable, pairwise
disjoint, and cover the group. The proof applies `hasSum_integral_iUnion`.

`setIntegral_matrixIntegrand_determinantSlice` identifies the integral of the
actual matrix integrand at exponent `s+r/2`, with coefficient function
`χ(det h) f(h)`, over determinant slice `m` as `b(m) z^m`.
The determinant power splits at `s+r/2`, its `s` part is constant on the slice,
and the indicator integral is exactly the displayed coefficient.
This identity of totalized integrals alone makes no convergence claim.

`adjacentRankMatrixSliceExpansion` separately assumes
`GodementJacquet.Padic.MatrixConverges` at that shifted parameter. It proves
absolute summability of `b(m) z^m` and its `HasSum` to the actual
`GodementJacquet.Padic.matrixIntegral`. The integral partition gives the sum,
and complex finite dimensionality gives absolute summability.

For an actual ambient Whittaker function `U` and inverse-character function
`W'`, `corankOneIntegrand_eq_mul_spectralPoint_zpow` proves on quotient slice
`m` that the corank-one integrand at `s` is its value at zero times `z^m`.
Its exponent `s-1/2` splits as `-1/2+s`. Quotient induction and the existing
normalized determinant-power formula prove the identity.

`corankOneSliceExpansion` uses any Borel quotient measure `ν` and assumes
global integrability at `s`. It proves absolute summability of
`sliceCoefficient (corankOneIntegrand ... 0) m * z^m` and its `HasSum` to the
actual corank-one integral. The existing quotient partition and norm bound in
`EqualRankSliceExpansionProof` apply after the pointwise spectral identity.

## Scope

All convergence premises are genuine `Integrable` assertions for the actual
integrands. No assertion about a totalized integral supplies those premises.
No induced-model realization, full Whittaker-type assertion, rational factor,
functional equation, or parent gamma/L certificate is concluded. The actual
finite coefficient convolution, common right half-plane, finite product
identity and final factor assembly retain their separate proof obligations.
