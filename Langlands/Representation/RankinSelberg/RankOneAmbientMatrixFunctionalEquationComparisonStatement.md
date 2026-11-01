# Rank-one comparison from an ambient matrix functional equation

Authors: Worker 468 (prepared statement and documentation); Worker 623
(original-source audit and final documentation); Worker 396 (contributing
source and predicate audit).

This pair defines the internal closed proposition
`Langlands.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonStatement.{uF,uV,uW}`.
It supplies a statement for independent review, with no proof or assertion that
its analytic premises hold. It extends the conditional matrix-to-rank-one
interface by locating its normalized matrix data on a separate actual
representation whose coefficients contain those of the Whittaker model.

## Exact scope

The telescope retains every prime `p`, every `F : PadicField.{uF} p`, the
canonical field topology, valuation and local-field structure, the Borel
measurable space, and the derived separation and total-disconnectedness
instances used by self-duality. It quantifies every bundled nontrivial unitary
additive character `ψ` and every supplied additive Haar measure `ν` with
`IsSelfDual ψ ν`. The same `ν` occurs in both the premise and the conclusion.

For every `n : ℕ`, including `n = 0`, the original representation `σ` is an
actual complex representation of `GL_(n+1)(F)` on an arbitrary complex module
`V : Type uV`. Its sole representation hypothesis is full
`IsOfWhittakerType n (standardCharacter ψ n) σ`: smooth admissibility, finite
generation over the group algebra and a linear equivalence of the entire
functional space with `ℂ`. Every nonzero standard Whittaker functional `ℓ`
is quantified. Reducible `σ` are retained.

Next come every independent complex module `W : Type uW` and actual
representation `ρ` of the same group on `W`. The new premise is the actual
submodule inclusion

```text
GodementJacquet.biSmoothMatrixCoefficients
  (glModelRepresentation ψ n σ ℓ)
    ≤ GodementJacquet.biSmoothMatrixCoefficients ρ.
```

The left carrier is exactly
`(glCoefficientModel ψ n σ ℓ).toSubmodule`. Thus the premise concerns actual
complex functions on the group, with the published smooth-vector and
smooth-functional coefficient span. It does not identify `σ`, its coefficient
model or `ρ` by an equivalence. It assumes no subquotient occurrence or
irreducibility. All three universes `uF`, `uV`, `uW` are independent. No
additional smoothness or admissibility hypothesis on `ρ` is imposed.

For every fixed `P PDual : Polynomial ℂ`, `c : ℂˣ` and `a : ℤ`, assume the
unchanged predicate

```text
GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData
  F ψ ν ρ P PDual c a.
```

This is full data on `ρ`: common shifted convergence and rational continuation
for every full-matrix Schwartz test and every actual bi-smooth coefficient,
the normalized reciprocal generators `P` and `PDual` for the original and
inverse-transpose coefficient families, a Fourier witness for each test, and
the normalized matrix equation for all coefficients and continuation pairs.
The shift is `n/2`, the Fourier pairing is the plus trace-transpose pairing,
and the transform uses the product of the specified `ν`.
Both p-adic wrappers use `F.canonicalTopologicalData.residueCardinality`
and `normalizedAbsoluteValue F.canonicalTopologicalData`. The matrix group
measure is the published `generalLinearHaar F.Carrier n`; the pair
certificate uses the published group and unipotent Haar measures of its
smaller rank. No replacement normalization of `ν` is made.

The conclusion is exactly

```text
IsPadicSymmetricGammaFactor F ψ ν σ
  (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
  (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual).
```

For `q` the canonical residue cardinality, this rational gamma expression is
`c X^a P(X) / PDual(q⁻¹/X)`. The symmetric wrapper keeps the existence of a
compatible quotient measure (with right-invariant unipotent Haar measure),
the existence of nonzero standard and inverse-standard functionals on the
two representations, and the equation for every compatible quotient measure
and every pair of nonzero functionals. For `n > 0` it includes every
complementary pair `j, k` with `n = j + k + 1`, and requires a nonzero
rational integral value for each such block. For `n = 0` it is the equal-rank
equation: some model integral has nonzero rational continuation, and every
model vector pair and every Schwartz row test admit the Fourier and
continuation witnesses required by the certificate. In both cases the
minus-one model scalar and all continuation witnesses are retained. The
functional equation holds on the full reduced-denominator domain of the
rational factor, including points made regular by cancellation of the
displayed expression.

## Provenance and intended proof boundary

Registered original: Jacquet–Piatetski-Shapiro–Shalika, *Automorphic forms on
GL(3) I* (1979), source `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed p.177 (one-based PDF p.10) fixes the matrix integral and Fourier
convention. Proposition 3.1, printed pp.185–187 (PDF pp.18–20), uses compact
averaging to turn model functions into matrix coefficients. Remark 2.2.5,
printed p.183, and Remark 4.2, printed p.190 in the discussion on pp.188–190,
permit admissible finitely generated right-translation spaces. Section 4.4,
printed p.194 (PDF p.27),
explicitly allows Theorem 4.5 in that setting when the corresponding
Whittaker-side equation is supplied. Theorem 4.5 and its proof, printed
pp.194–198, compare every complementary pair of rank-one blocks. The
registered pointer and the available project/Library errata locations were
checked; no source-specific erratum for these passages was located.

The ambient coefficient inclusion is an internal extension of this argument,
rather than a transcription of a numbered theorem. Compact averaging gives
actual coefficients of the model, which the inclusion places in the ambient
family. Convergence, continuation witnesses and the matrix equation can then
be restricted to those coefficients. The ambient dual generator supplies its
own polynomial nonvanishing. A proof must retain the supplied measure,
perform the signed-to-unsigned Weyl conversion, and establish the full
functional and quotient-measure quantifiers. The source's conductor-zero
reduction is not an extra hypothesis of this statement: the compact-open
Fourier argument must work for the given character and its annihilator
lattices with the supplied self-dual `ν`. The existing published
`RankOneMatrixFunctionalEquationComparisonStatement` and its proof cover the
special case of matrix data on the model itself; they do not supply this
ambient extension by an immediate application.

The source block theorem has empty range at `n = 0`. That boundary therefore
requires a separate rank-one argument with the actual character model and
one-by-one matrix/row Fourier identification. In particular, a proof cannot
obtain a nonzero model integral by extracting an ambient generator witness:
coefficient inclusion is only one direction. It must establish a nonzero
model integral independently, for example from a model function nonzero at
the identity and a sufficiently small compact-open Schwartz test. Full type
and nonzero `ℓ` remain the only representation premises; this witness is a
proof obligation, not a new assumption.

JPSS (1983), source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
Section 5.4, printed pp.422–423 (PDF pp.57–58), motivates applying a matrix
equation on an induction of generic block socles to coefficients of its
actual generic constituent. Any such application still requires actual
occurrence, coefficient inclusion, and transport from a constituent to its
coefficient model. Relating its gamma factor to the original reducible
representation remains another obligation. This pair supplies none of those
results and makes no L-divisibility or multiplicativity claim.

The ambient polynomials are never asserted to generate the constituent's
matrix rational values. Inclusion of coefficients can shrink that family;
it does not identify its normalized generator. This distinction is the
purpose of the separate conditional interface.
