# Matched original and dual rational finite products

This derived prerequisite implements the common-half-plane and rational
continuation form of the matched determinant-coefficient formulas in
JPSS Section 6.3, formulas (10) and (14). It uses the actual original and
literal model-star coefficients already proved, together with the
published equal- and unequal-rank analytic theorems and the finite-product
continuation theorem. Actual matrix rational-value witnesses remain
explicit inputs.

`AdjacentRankProductContinuationData` records the conclusion for one
supplied finite family. It asserts the existence of rational values `A_i`
of the actual equal-rank quotient integrals, and one right half-plane on
which the actual corank-one integral, every equal-rank factor, and every
shifted matrix factor converge and satisfy

```text
corankOneIntegral(U,W',s)
  = c * sum_i equalRankIntegral(W,B_i,phi,s)
       * matrixIntegral(Phi,s+r/2,chi(det)*f_i).
```

It also asserts the rational continuation
`RatFunc.C(c) * sum_i A_i*M_i` of that actual corank-one integral and
uniqueness of this rational value. The coefficient, group and quotient
normalizations are exactly those of the supplied canonical p-adic field
and the unchanged compatible quotient and group Haar measures.

`corankOneCoefficient_scalarProductContinuation` adds a nonzero unit
scalar to the already implemented coefficient-model continuation theorem.
It retains the supplied finite family and all actual matrix witnesses.
If the actual coefficient of `U` is `c` times the finite convolution,
replace only its ambient model vector by `U0=c^-1*U`. The actual
corank-one integrand is linear in that vector, as proved by quotient
representatives, and the published restricted-coefficient linearity
cancels `c`. Apply the existing
`corankOneCoefficient_productContinuation` to `U0`, with the unchanged
first vector, finite family, row test and matrix functions. That theorem
derives all quotient convergence and equal-rank rationality from the
actual full Whittaker-type coefficient images and the supplied nonzero
functionals. Multiplying its actual integral identity and continuation
by `c` gives the claimed result for `U`. The equality
`c*U0=U` transfers genuine corank-one convergence as well. Continuation
uniqueness uses the actual residue cardinality greater than one.

For original inner rank `n=r+1`, the matched theorem starts with full
Whittaker-type representations `sigma,tau,pi`, where `sigma` and `pi`
use the standard character for `psi`, and `tau` uses that for
`psi.scale(-1)`. All three specified functionals are nonzero, and all
three vectors belong to their specified actual coefficient images.
The ambient vector `U` is explicitly realized by the separated
rectangular model from the square test `Phi`, row test `phi`, and first
model vector `W`. A supplied `phiHat` is an actual plus row Fourier
partner for `phi` with the same supplied self-dual scalar Haar.
The theorem uses

```text
PhiD(X) = PhiHat(-X),
WD(g) = W(w_n*iota(g)),
UD(g) = U(w_(n+1)*iota(g)),
cD = chi^-1(det(-I_n)).
```

The transformed first and ambient vectors belong to the actual
inverse-transpose pullback coefficient images. The published dual
Whittaker-type theorem transports admissibility, finite generation and
the entire one-dimensional functional space; it does not identify the
pullback representation with a contragredient or with an original
carrier. Nonvanishing of each transformed functional follows from the
actual Weyl-translation formula.

`adjacentRankModel_matchedProductContinuation` chooses `N` and one family
`B` in the original second coefficient image before the input second
vector `W'`, and one family of actual bi-smooth image-representation
matrix coefficients `f_i` before all spectral parameters and matrix
rational-value witnesses. For any actual shifted rational values `M_i`
of `Phi,chi(det)*f_i` and `MD_i` of
`PhiD,chi^-1(det)*coefficientIota(f_i)`, it proves the two product
continuation assertions with those exact witnesses. The original
assertion has scalar one. The transformed assertion has scalar `cD`,
uses exactly `dualModelLinearMap(B_i)`, and uses exactly
`coefficientIota(f_i)`. Each assertion includes an actual common right
half-plane for all its factors; the two assertions need not have the
same threshold. Their rational values are uniquely determined.

The proof obtains the actual matched coefficient formulas once, invokes
the scalar continuation theorem for the original coefficient images,
and invokes it again for the actual transformed images. The latter use
the same group Haar, quotient Haar, scalar Haar, finite choices and
determinant conventions. No second finite-family choice is made. The
Fourier action in the underlying model-star restriction remained fixed
at the original `psi` before the resulting coefficient function was
recast along the character equality.

The first, second and ambient carriers and the field retain independent
universes, and the carriers have only algebraic additive and
complex-module structures. Reducible full Whittaker-type
representations and every natural `r`, including actual inner rank one,
are retained. The nonzero-functional hypotheses are those required by
the already published quotient analytic theorems for these intermediate
coefficient models. The ambient full-type and realization hypotheses
are explicit intermediate data, not new premises of either parent
gamma/L target.

The source is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in preceding work, and
pp.435–437 were visually reread for the transformed calculation.
The same-family display on p.437 transforms the original expansion
before (14). The scalar-normalization argument for applying an existing
continuation theorem is an internal implementation choice. The earlier
bounded registered-source and correction-note audit found no
JPSS-specific registered erratum.

This module proves the two matched global rational finite-product
identities conditional on the displayed actual matrix-value witnesses.
It does not prove existence of those witnesses, construct the ambient
model realization, compare the two rational values by functional
equations, perform normalized lower-to-upper transport, or prove either
parent gamma/L factor statement.
