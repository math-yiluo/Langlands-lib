# Adjacent-rank model-star identity with the Fourier character fixed

This module defines the closed source-derived proposition
`Langlands.RankinSelberg.AdjacentRankModelStarStatement.{uF,uV}`.
It supplies no proof. It is an explicit scalar-integral formulation of the
model identity displayed in JPSS Section 6.2 Proposition (1), with the
Fourier action and coefficient characters kept distinct.
The formulation is based on Worker 486's draft, with source and
constructor checks and expanded provenance by Worker 350.

For every prime p and canonical p-adic field F in universe uF, the
character psi, scalar additive Haar nu and its self-duality certificate
remain supplied. Put n=r+1 and t=r+2, for every natural r including zero.
The representation sigma of GL_n acts on its original complex module V
in independent universe uV and has the published full standard
`IsOfWhittakerType`. Reducible representations remain included. Each
standard-psi functional ell, continuous quasicharacter chi, whole algebraic
test tensor Psi and ambient g in GL_t is quantified. The character psi is
the supplied nontrivial continuous unitary additive character. There is
no nonzero-functional restriction: ell may be zero. There is no topology
or norm on V or its actual coefficient image, no large-twist restriction,
and no assumed identity, convergence or factor existence.
The full type condition retains admissibility (including smoothness),
finite generation over the group algebra, and an exactly one-dimensional
space of standard-character functionals.

Write

```text
K(h) = [h, (h^(-1))^transpose epsilon],
iota(h) = (h^(-1))^transpose,
w_n = weylLong n F,  w_t = weylLong t F,
zeta = diag(-1,...,-1,1),  k = zeta*g,
H = rectangularFourierEquiv psi nu n t hself,
PsiH = (H tensor identity)(Psi).
```

These are the existing literal constructors. The tensor map changes only
the Schwartz factor, leaving the original actual coefficient image as its
second factor. The vector epsilon is the last standard basis column;
both long Weyl representatives have ones on their anti-diagonals.
The full plus-psi Fourier transform is

```text
(H Phi)(m) = integral Phi(a) * psi(sum_i sum_j a_ij * m_ij) da,
```

where da is `rectangularMeasure nu n t`, the nested product of the
supplied scalar Haar nu over all entries. It is distinct from the
last-column partial Fourier transform that defines rho0.
The tensor map acts on the whole tensor product. Let E be the published
`adjacentRankTestEvaluation psi sigma ell` and let rho be the published
`adjacentRankRho0 psi nu hself sigma ell`. Define

```text
I(h) = E(rho(k) PsiH)(K(h), w_n*iota(h^(-1)))
       * chi^(-1)(det h) * |det h|^(r/2).
```

The proposition asserts convergence of the existing source model integrand
at `w_t*iota(g)`, integrability of I, and

```text
adjacentRankModelIntegral(psi,chi,Psi)(w_t*iota(g))
  = chi^(-1)(det k) * |det k|^(n/2) * integral I(h) d_eta(h).
```

Here `eta = generalLinearHaar F.Carrier r` is exactly the shared Haar on
inner GL_n, normalized on its integral points. Every determinant weight
uses `normalizedAbsoluteValue F.canonicalTopologicalData` and the existing
complex-power convention. All additive transforms use the supplied nu.
In particular `|det h|^s` is
`(abv (Matrix.det h.val) : ℂ) ^ s`, with `abv` the canonical normalized
absolute value, so a uniformizer has absolute value q^(-1).
Both sides use the same eta; no new measure normalization is chosen.
The source convergence assertion is the existing
`Padic.AdjacentRankModelConverges`, so the displayed equality is accompanied
by actual integrability on both sides.

## Coefficient character and action character

On a pure tensor Phi tensor W the right integrand is exactly

```text
rho0_psi(k)(H Phi)(K(h)) * W(w_n*iota(h^(-1)))
  * chi^(-1)(det h) * |det h|^(r/2).
```

The transformed coefficient `D W(a) = W(w_n*iota(a))` has inverse
standard psi character and is a coefficient of the actual
`inverseTransposePullback sigma`, with functional
`dualFunctional psi sigma ell`. This follows from the already published
Whittaker dual constructions; no smooth-contragredient identification or
injectivity of the original coefficient map is asserted. The original
coefficient is simply evaluated at its transformed argument, so the Lean
formula needs no equality cast between distinct character spaces.

The Fourier action remains `rho0_psi` on both sides. Replacing the right
side with `adjacentRankModelIntegral` at psi.scale(-1) would also change
the action character, which is a different formula. The existing
`adjacentRankStarEquiv` at psi takes a functional for psi.scale(-1),
with inverse-character coefficients as its source and standard-character
coefficients as its target. Its full Fourier factor is plus psi, as required by the opening
star definition in the source. This module does not identify that
particular typed map with the displayed formula for standard-psi source
coefficients. It expands the coefficient transformation directly and
retains the same Fourier action.

## Source and derived scope

The registered source is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983),
367-464, source ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original PDF is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Workers 486 and 350 visually read printed 427-429 for the right action, partial
transform, rho0, plus full transform and literal model (8), and printed
431-432 for the Section 6.2 opening definition, Proposition (1), scalar
Lemma (2) and its Fourier-inversion reduction. These are one-based PDF
pages 62-64 and 66-67. No source-specific registered errata was found in
prior bounded project checks.

Printed 431 first defines a star map on inverse-character coefficients,
then displays its Proposition for standard-character coefficients.
The statement here makes the underlying function formula for that
displayed Proposition explicit. On its left, the ambient
Weyl/inverse-transpose transform evaluates the original model at
`w_t*iota(g)`. To expand its right, substitute the full plus-psi transform
H, the coefficient transform D, the inverse quasicharacter chi^(-1), and
ambient argument k=zeta*g into the literal formula (8), while retaining
the Section 6.1 action rho0_psi. Since rho0 acts only on the Schwartz
factor, its pure-tensor coefficient is
`D W(h^(-1)) = W(w_n*iota(h^(-1)))`. Formula (8) then gives exactly the
outer determinant exponent n/2, inner exponent r/2, and I displayed
above. Linearity extends this interpretation to every algebraic tensor.
This is a character-separated expansion of the source's displayed
identity; it does not treat the opening typed star map as a map on
standard-character source tensors.

Both integrability assertions are included to express the displayed
identity as an equality of convergent scalar integrals. For the source
side, Section 6.1 asserts convergence of (8) before its separate
large-positive-twist image assertion. The published
`adjacentRankModelConvergence` already proves this source convergence
for every chi. Its support argument uses smoothness and Schwartz support;
it needs neither an image assertion nor a large twist.

For the target side, H and rho0_psi(k) preserve the Schwartz space.
The coefficient D W is an actual inverse-character coefficient of
`inverseTransposePullback sigma` by `dualFunction_coefficient` and
`dualFunctional`; smoothness is preserved by
`inverseTransposePullback_isSmooth`. The same simple-root support argument
used by `adjacentRankPure_hasCompactSupport` therefore applies to this
inverse nontrivial unitary character and the resulting Schwartz factor.
It gives compact support on inner GL_n for each pure-tensor product
appearing in I. These scalar functions are continuous, and multiplication
by the continuous inverse quasicharacter and determinant weight preserves
compact support. Integration against the shared locally finite Haar and
finite tensor sums explains the asserted target integrability without a
growth or convergence premise. This is a derived justification for its
inclusion, not an implemented proof of that conjunct in this module.
It does not change the action character to obtain a different target
model integral.

The explicit function formula, original-carrier tensor packaging,
canonical p-adic scope, full-type hypothesis and both integrability
conjuncts are thus derived scope choices, rather than a claim that JPSS
provides this typed statement verbatim. A later proof must establish the
literal equality and target integrability under these exact conventions.

The scalar `AdjacentRankUnipotentFourierStatement` is a separate prerequisite,
not assumed in this proposition. The existing convergence proof concerns
the original standard-character model only and does not by itself prove
this identity. The proposition asserts no induced-model image equality,
normalized-type theorem, determinant-shell expansion, functional equation,
gamma factor or L polynomial.
