# Finite coefficients of the middle compact average

Worker 486 implements the finite-basis step in JPSS Section 6.3, formula
(7), printed 434. The module constructs the actual compact projection and
its finite basis, smooth-dual coordinate functionals and actual bi-smooth
matrix coefficients. Its p-adic theorem proves the resulting scalar Haar
average identity on the specified coefficient model.

## Algebraic constructions

The declarations in `Langlands.Compact` apply to a topological group G and
an admissible complex representation rho on an arbitrary complex module V.
The group and carrier universes are independent. The only compactness
hypothesis is that the given open subgroup K is compact. No topology,
norm or completeness is placed on V, and neither irreducibility nor finite
generation over the group algebra is assumed.

`averageToFixed` is the published finite-orbit `Compact.averageMap`, with
codomain restricted to `fixedVectors rho K`. The proof
`averageToFixed_translate` uses `Compact.orbitMean_apply` to show that
P(rho(k)v)=P(v) for k in K. Admissibility makes this actual fixed-vector
space finite dimensional. `fixedBasis` chooses its `Module.finBasis`,
indexed by `Fin (Module.finrank ...)`, before the input vector.

`averageCoordinate rho hadm K hK i` is b.coord(i) composed with P. It is an
actual `SmoothDual rho` vector: translation invariance of P proves that
this algebraic linear functional is fixed by K in the dual action.
`averageCoefficient rho hadm K hK v i` is the bi-smooth coefficient
`h -> averageCoordinate(i)(rho(h)v)`, as a member of the actual
`GodementJacquet.biSmoothMatrixCoefficients rho` span. Smoothness of v
comes from admissibility. `averageToFixed_expansion` applies the fixed
basis expansion to P(rho(h)v), then includes that equality into V.

`finiteAverageCoefficients` packages this as

```text
there exist m and B : Fin m -> V such that
for every v there are f_i in biSmoothMatrixCoefficients rho such that
for every algebraic linear functional Lambda and every h,
Lambda(P(rho(h)v)) = sum_i Lambda(B_i) * f_i(h).
```

Thus the number and first-variable vectors are chosen before v, Lambda
and h; the f_i are chosen after v and before Lambda and h. The proof
applies Lambda to `averageToFixed_expansion`. These generic constructions
are internal linear-algebra packaging of the source's projection/basis
argument, not separate verbatim assertions from JPSS.

## Actual p-adic middle average

`Langlands.RankinSelberg.Padic.adjacentRankCompact_middleAverage` retains
every prime and canonical p-adic field F in universe uF, actual rank r+1
including rank one, supplied unitary additive character psi, admissible
representation sigma on its original complex module V in independent
universe uV, specified standard-psi functional ell, and arbitrary compact
open subgroup K. The functional and model vector may be zero. There is
no full-type, nonzero-functional, Fourier-measure or self-duality premise.
An inverse-character source coefficient may be handled by substituting
psi.scale(-1).

Let M be the actual coefficient image of ell and tau its actual
right-translation representation. The theorem constructs finitely many
B_i in M, before every input W in M. For each W it constructs actual
f_i in `GodementJacquet.biSmoothMatrixCoefficients tau`, before both
group elements g,h, and proves

```text
mass(K)^(-1) * integral_K W(g*k*h) d_eta(k)
  = sum_i B_i(g) * f_i(h).
```

Here eta is exactly `generalLinearHaar F.Carrier r` on the actual GL_(r+1),
normalized on its integral subgroup. Its real mass of K is embedded in
complex scalars. The theorem does not replace it with a newly chosen
measure. The B_i remain in the specified coefficient image of the original
sigma; no injectivity of its coefficient map or realization by all
equivariant functions is assumed. The f_i are coefficients of this actual
model representation, as stated, rather than automatically coefficients
of a different constituent or of an induced representation.

The proof imports unchanged published helpers. Admissibility passes from
sigma to M by `GodementJacquet.Padic.glModel_isAdmissible`, which uses the
actual surjective model map and admissible-quotient theorem. Applying
`Compact.finiteAverageCoefficients` gives B_i and f_i. For fixed g, the
scalar point-average functional A_g from
`GodementJacquet.Padic.modelPointAverage` is invariant under K.
`GodementJacquet.apply_averageMap_of_invariant` therefore identifies
A_g(tau(h)W) with A_g(P(tau(h)W)). The latter is mass(K) times evaluation
at g, by `modelPointAverage_of_mem_fixedVectors`. The imported construction
justifies its scalar integrals using continuity on compact K. Openness
and compactness give finite positive Haar mass, through
`measureReal_openSubgroup_ne_zero`. After cancellation, the generic finite
expansion with the algebraic evaluation functional gives the displayed
identity. No Bochner integral in M and no extra identification of finite
averages with Haar integration is assumed.

## Source and scope

The original is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Worker 486 visually reread printed 433-436 (one-based PDF pages 68-71),
especially the compact subgroup choice and formula (7) on printed 433-434.
No source-specific registered errata was found in prior bounded project
checks. The implementation follows its admissibility/basis argument,
using published algebraic finite-orbit projection and scalar point averages.
Its admissibility-only scope and generic constructors are derived choices.

This helper supplies the finite middle-average step. It does not choose K
to fix a square Schwartz test or quasicharacter, impose transpose stability,
prove joint-integrability or determinant-shell convolution, or assert any
adjacent-rank zeta, gamma or L-factor identity.
