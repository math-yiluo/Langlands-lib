# Actual reflected matrix integrals and the adjacent-rank sign

This derived prerequisite implements the square-test reflection and
central scalar calculation following JPSS Section 6.3 formula (14) on
printed p.437. It retains the actual bi-smooth matrix coefficients of
the specified Whittaker coefficient-image representation, the inverse
determinant character, and the unchanged canonical general-linear Haar.

For actual inner rank `n=r+1`, write `c=-I_n`. If `zeta` is a supplied
`HasModelMinusOneScalar` for the second representation and its specified
functional, `biSmoothModelCoefficient_minusOne` proves
`f(c*g)=zeta*f(g)` for every actual bi-smooth coefficient `f` of that
coefficient image's right-translation action. Right translation by the
central `c` acts on every vector in the image by that scalar, by the
given model predicate. The proof applies this action formula to each
spanning coefficient and extends it over the whole coefficient span by
addition and complex scalar multiplication. No irreducibility or
central character on the original possibly reducible carrier is assumed.

Inverse transpose fixes `c`. The theorem
`adjacentRankDualMatrixCoefficient_minusOne` therefore proves that the
literal dual twisted function

```text
v(g) = chi^-1(det g) * coefficientIota(f)(g)
```

satisfies `v(c*g)=eta*v(g)`, with the actual nonzero unit scalar

```text
eta = adjacentRankDualMatrixReflectionScalar F chi r zeta
    = chi^-1(det c) * zeta.
```

The proof uses inverse transpose's multiplicativity, the unchanged
coefficient `f`, and the determinant character's multiplication law.

For any supplied raw group function `v` with this scalar reflection law
and any square Schwartz test `Phi`, `adjacentRankMatrix_reflection`
proves equivalence of actual absolute convergence of the matrix
integrals for `Phi` and `Phi(-X)`, at every complex exponent, and the
literal integral identity

```text
matrixIntegral(Phi(-X),s,v) = eta * matrixIntegral(Phi,s,v).
```

Left multiplication by the actual `c` preserves the same GL Haar
measure. Its determinant absolute value is one. The reflected
integrand after this measure-preserving substitution is exactly `eta`
times the original integrand. Integrability is transported by the
measurable embedding and equivalence of integrability under
multiplication by a nonzero scalar. The integral identity uses that
same substitution and scalar linearity and is valid for totalized
integrals as well.

`adjacentRankMatrix_reflectedRationalValue` transports an actual shifted
rational-value witness `M` for `Phi,v` to the witness
`RatFunc.C(eta)*M` for `Phi(-X),v`. The convergence half-plane is
retained by the proved equivalence, and scalar continuation followed by
the proved whole-function integral equality gives the actual rational
continuation. Thus this is transport of genuine analytic witnesses and
does not infer convergence from totalized integral equality.

`adjacentRankModelStar_reflectionScalar_cancel` proves

```text
adjacentRankModelStarScalar(F,chi,r) * eta = zeta.
```

The scalar matrix `scalar(-1)` is the actual negative identity. The
determinant character evaluated on it squares to one, by the group and
character homomorphism laws. This cancels the two copies of
`chi^-1(det c)` exactly. The rational finite-sum cancellation theorem
retains the same indexed quotient values `A_i` and matrix values
`M_i` and gives

```text
C(chi^-1(det c)) * sum_i A_i * (C(eta) * M_i)
  = C(zeta) * sum_i A_i * M_i.
```

This is the single additional model-minus-one factor needed when
combining the equal-rank and matrix functional equations in the
adjacent-rank calculation. The theorem itself asserts the literal
algebraic cancellation and no functional-equation conclusion.

The canonical field and original representation carrier retain
independent universes. The carrier has only algebraic additive and
complex-module structures. Every natural `r`, including actual inner
rank one, zero specified functionals and reducible inputs are retained.
`HasModelMinusOneScalar` is supplied intermediate data; its full-type
existence is already a separate published API. The generic reflection
theorems need only the displayed scalar function law, without any
matrix-coefficient membership assumption.

The original is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in preceding work; p.437 was
visually reread for this calculation. After (14), the source identifies
the matrix integral with reflected square test by the central
minus-one scalar of the inverse-transpose determinant twist. The two
sign-character factors then cancel. The implemented scalar and
coefficient-image proof give that calculation without assuming a
central character on an original reducible carrier. The earlier bounded
registered-source and correction-note audit found no JPSS-specific
registered erratum.

Existence of actual matrix analytic witnesses, the ambient model
realization, full functional-equation assembly, normalized
lower-to-upper representation transport and both parent gamma/L
statements remain separate obligations.
