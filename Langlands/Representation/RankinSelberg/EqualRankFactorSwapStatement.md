# Equal-rank exchange of p-adic pair-factor certificates

Author: Worker 88.

The module defines the proposition
`Langlands.RankinSelberg.EqualRankFactorSwapStatement.{uF, uV, uW}`.
It states exchange of the two actual representations in the existing L,
epsilon and gamma certificate relations. It supplies no proof or axiom.

## Exact scope

For every prime `p`, every `F : PadicField.{uF} p` with its canonical
topological data, every `UnitaryAdditiveCharacter F.Carrier` named `ψ`,
every supplied `SelfDualHaar F.canonicalTopologicalData ψ` named `ν`, and
every `n : ℕ`, let `π` and `σ` be actual complex representations of
`GL_(n+1)(F)` on `V : Type uV` and `W : Type uW`, respectively. The three
universes are independent. The character structure includes continuity,
unitarity and nontriviality; the supplied measure is self-dual for that
character. No existence of such a measure is asserted here.

Both representations are assumed to satisfy
`IsOfWhittakerType n (standardCharacter ψ n)` in the canonical topology.
This is the existing conjunction of admissibility (including smoothness),
finite generation over the group algebra, and an exactly one-dimensional
space of Whittaker functionals. There is no irreducibility hypothesis and
no finite-dimensionality requirement on `V` or `W`.

The conclusion is the conjunction of three equivalences:

- For every `P : ℂ[X]`, `IsPadicPairLPolynomial F ψ ν.val π σ P` if and
  only if `IsPadicPairLPolynomial F ψ ν.val σ π P`.
- For every `e : ℂˣ × ℤ`, the same equivalence for
  `IsPadicPairEpsilonFactor`, preserving the coefficient and exponent in `e`.
- For every `G : RationalFunctions`, the same equivalence for
  `IsPadicPairGammaFactor`, preserving `G`.

All three use the same `ψ` and `ν.val` on both sides. For residue cardinality
`q`, the certificates represent `L(s) = 1/P(q^(-s))`,
`ε(s) = e.1 * q^(-e.2*s)` and `γ(s) = G(q^(-s))` in the existing relations.
Those relations, including their compatible quotient measure existence and
universal quantifiers, are used unchanged. The epsilon and gamma relations
also retain their nonzero functional and universal functional-equation
requirements. No factor existence or additional analytic conclusion is
added to the proposition.

## Original source and interpretation

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained PDF is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
PDF page numbers below are one-based and include its cover.

Section 2.1, printed pages 385–386 (PDF 20–21), defines representations of
Whittaker type without irreducibility and explains transport between the
characters `ψ` and its inverse. The statement specializes the source's
non-Archimedean field setting to the Library's p-adic fields. The common
source rank `r = t` is `n + 1` here, including rank one.

Section 2.12, printed page 403 (PDF 38), first establishes independence of
the L-factor from the nontrivial additive character by diagonal translation
and a change of variables. It then explicitly asserts, for equal ranks,
`L(s, π × σ) = L(s, σ × π)` and
`ε(s, π × σ, ψ) = ε(s, σ × π, ψ)`. Only for unequal ranks does it introduce
the convention of reading the larger rank first. Thus the definitions
`IsPadicSymmetricLPolynomial`, `IsPadicSymmetricEpsilonFactor` and
`IsPadicSymmetricGammaFactor` alone do not establish this equal-rank target.

Gamma symmetry is a derived consequence, rather than an explicit assertion
of Section 2.12. Section 3.1, display (2), printed page 404 (PDF 39), defines

`γ(s, π × σ, ψ) = ε(s, π × σ, ψ) * L(1-s, π^ι × σ^ι) / L(s, π × σ)`.

Here `π^ι` and `σ^ι` are inverse-transpose pullbacks on the original
carriers, as in Section 2.1. The formula uses the L-polynomials of both the
original and these dual pairs. We do not identify these pullbacks with
smooth contragredients for a possibly reducible representation. The
certificate formulation is the Library's relational expression of the
source equalities, not a new definition of the factors. No project errata
file for this registered source was present at preparation.

## Expected proof dependencies

A future proof must transport the Whittaker models between `ψ` and
`ψ.scale (-1) = ψ⁻¹`. The integrals for `(π, σ)` use a `ψ` model for the
first member and a `ψ⁻¹` model for the second. Merely interchanging the two
Whittaker functions therefore gives the reversed pair at the inverse
character; it does not directly identify the two fixed-`ψ` integrand
families in this target. The L-factor argument must supply the
additive-character independence described in Section 2.12, respecting the
quotient measure and normalized generator. The epsilon argument must also
transport the Fourier transform, self-dual measure and model minus-one
scalar in the functional equation of Theorem 2.7(iii), printed page 391
(PDF 26). Epsilon independence from the additive character is not assumed.

For gamma, a proof may use the epsilon/L-ratio formula with the original
and inverse-transpose dual normalized polynomials, their exchange laws,
and uniqueness of the gamma relation. The Library's
`IsEqualRankEpsilonFactor.gammaFactor` in `EqualRankGammaFactor` is a
conditional bridge: its original and dual analytic conclusions and
polynomial certificates must be supplied, not inferred from its existence.
Any needed existence, character transport, analytic and functional-equation
results remain proof dependencies, not hypotheses silently added to this
statement. This module imports only the established factor definitions
through `PadicPairFactors`; it does not assume any of those proof targets.
