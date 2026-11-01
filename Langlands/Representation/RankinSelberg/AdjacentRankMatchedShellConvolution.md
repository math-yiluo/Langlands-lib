# Matched original and transformed adjacent-rank shell convolutions

This derived prerequisite implements the actual outer quotient calculation
with the same finite inner-separation data on the original and transformed
sides. It extends the fixed-shell calculation already implemented in
`AdjacentRankShellConvolution` and applies the simultaneous inner identities
from `AdjacentRankMatchedInnerSlices`. Its source is JPSS Section 6.3,
printed pp.434–437, formulas (7)–(10) and the transformed compact-average
identity preceding (14).

## Actual functions and conclusion

Let `T = F.canonicalTopologicalData`, `G = GL_(r+1)(F)`,
`Q = N_(r+1) \ G`, and `eta = generalLinearHaar F.Carrier r`.
The quotient measure `nu` is supplied and compatible with the same group
and unipotent Haar measures. Every topology, valuation, absolute value and
determinant order is canonical; no measure is renormalized.

`AdjacentRankShellConvolutionAt` is a proposition describing the literal
finite convolution for specified data. For standard and inverse Whittaker
functions `W,W'`, square test `Phi`, row test `phi`, character `chi`,
finite inverse-character family `B_i`, functions `f_i` and lower bounds
`Lq,Lh`, write

`a_s(h) = chi(det h) |det h|^s`,

`b_(j,s)(h) = 1_{ord(det h)=j} Phi(h) a_s(h)`.

The actual joint-shell kernel on representatives is

`K_(m,s)(Ng,h) = 1_{ord(det g)+ord(det h)=m}`
`  * W(g) W'(gh) phi(lastRow g) Phi(h) a_s(h)`.

Its before-shear kernel is the existing composition with inverse quotient
shear, with representative expression

`Kbefore_(m,s)(Ng,h) = 1_{ord(det g)=m}`
`  * W(gh^-1) W'(g) phi(lastRow(gh^-1)) Phi(h) a_s(h)`.

The proposition asserts genuine product-measure integrability of both
kernels, integrability of every equal-rank quotient-slice factor and every
inner group-slice factor, and the identities

`integral_(Q x G) K_(m,s) = sum_(Lq <= k <= m-Lh) sum_i`
`  equalRankSliceCoefficient(T,nu,psi,W,B_i,phi,k)`
`  * integral_G b_(m-k,s)(h) f_i(h)`,

and the same formula for the iterated integral of `Kbefore_(m,s)`.
All integer slices and complex exponents are included. This is a proposition
about existing actual functions and integrals; it is not an assumption of
an analytic continuation or a factor certificate.

`adjacentRankShell_finiteConvolution_of_innerSeparation` proves that
proposition for a supplied finite inner expansion. The first function
belongs to a specified actual coefficient image of a smooth representation.
The second function and each supplied `B_i` have inverse Whittaker covariance
and are continuous; each `f_i` is continuous. The hypotheses give actual
pointwise lower support bounds and the inner integral expansion for every
integer slice, complex exponent and external group argument. This theorem
makes no new finite-family choice.

`inverseCoefficientAsScaledStandard` transports the actual image of a
specified inverse-character functional to the actual image of that same
functional transported along
`standardCharacter_scale_neg_one`. It retains exactly the underlying
function and reuses the same original representation vector witnessing
image membership. Covariance alone is not used to assert model membership.

`AdjacentRankShellLowerBounds` records the actual pointwise lower bounds:
nonvanishing of `W(g)` and the row test implies `Lq <= ord(det g)`;
nonvanishing of the square test at `h` implies `Lh <= ord(det h)`.

## The matched theorem

`adjacentRankShell_matchedFiniteConvolution` starts with a smooth
representation `sigma` with standard functional and actual model vector
`W`, and an admissible representation `tau` with a specified functional
for `psi.scale(-1)`. Square tests `Phi,PhiD`, row tests `phi,phiD`, and
characters `chi,chiD` are arbitrary fixed inputs. No Fourier or inverse
relation between these inputs is assumed in this intermediate result.

The first transformed vector is the actual `dualModelLinearMap` image of
`W`, recast by `inverseCoefficientAsScaledStandard`. It belongs to the
coefficient image of `inverseTransposePullback sigma`, with functional
`dualFunctional` transported to the scaled-standard character. Its
underlying function is exactly
`g -> W(w_(r+1) * iota(g))`. Pullback along the actual continuous inverse
transpose preserves smoothness. No identification with a contragredient or
with the original carrier is asserted.

The theorem chooses four lower bounds, a finite size `N`, and one family
`B` in the specified actual coefficient image of `tau`, before the input
second model vector `W'`. It then chooses one family `f` of actual
bi-smooth matrix coefficients of that image's right-translation
representation, before every shell order `m` and exponent `s`.

Both `AdjacentRankShellConvolutionAt` assertions hold for those choices.
The original assertion uses the unchanged functions of `W'` and `B`,
recast as inverse functions for `psi`, and the functions `f_i`.
The transformed assertion uses first character `psi.scale(-1)`, the
recast dual first vector, second vector `dualModelLinearMap W'`, family
exactly `dualModelLinearMap B`, and matrix functions exactly
`coefficientIota f_i = f_i composed with iota`. The four explicit pointwise
support bounds cover the two fixed pairs of tests. The two convolutions
retain the same `N`, `B` and `f`, despite their potentially different
support intervals and arbitrary fixed second tests.

The field and the two original representation carriers have independent
universes. The carriers have only their algebraic additive and complex
module structures. Reducibility and zero specified functionals are
allowed. Every natural `r`, including actual group rank one, is retained.
No irreducibility, nonzero vector, growth estimate or half-plane premise
is added to these fixed-shell statements.

## Implemented proof

The reusable outer calculation is extracted from the existing
`adjacentRankShell_finiteConvolution` proof. Compatibility gives regularity
of the quotient measure. The published joint compact-support and
shear/Fubini result gives genuine integrability of both actual kernels and
of the outer integral. Compact support and continuity give the quotient
and group slice integrability assertions. A nonzero joint kernel has fixed
total order and both supplied lower bounds, so its quotient order belongs
to the finite interval `[Lq,m-Lh]`. The outer integral vanishes outside
that interval. Apply the existing finite determinant partition theorem.

On quotient slice `k`, the published pointwise kernel identity identifies
the group cutoff with slice `m-k`. Substitute the supplied inner expansion,
move its finite sum through the quotient integral using the proved slice
integrability, and identify the indicator integral with the existing
`equalRankSliceCoefficient`. The exact quotient shear then gives the
before-kernel formula with no scalar change.

For the matched theorem, obtain original and transformed support bounds
from the actual smooth coefficient images and the square tests. Apply
`adjacentRankInnerSlice_matchedFiniteSeparation` once to obtain `N,B,f`.
Apply the reusable outer theorem to its original and transformed inner
identities using those exact witnesses. Continuity of transformed model
and matrix functions follows by composition with the actual continuous
inverse-transpose map and long-Weyl multiplication. There is no second
existential choice of a finite family.

## Source and remaining scope

The original is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in the preceding work; printed
pp.435–437 were visually reread for the adjacent transformed calculation.
Formula (7) chooses a finite family before the second vector. The
complementary determinant orders in (9) give the finite coefficient
convolution underlying (10). The transformed compact-average display on
p.437 uses that same family with inverse transpose on its matrix
coefficients. Extracting the outer calculation for supplied data and
allowing arbitrary fixed second tests are internal formalization choices
preserving that source requirement. The earlier bounded literature audit
found no registered JPSS-specific erratum.

This unit proves actual matched fixed-shell integrals. It does not identify
the transformed before-kernel with the literal model-star diagonal
restriction, prove the global dual finite zeta-product formula (14),
provide rational matrix-value witnesses, prove model realization, or
establish either parent gamma/L statement. Spectral summation, analytic
continuation, functional equations and sign constants remain separate
assembly steps. No parent multiplicativity result is used.
