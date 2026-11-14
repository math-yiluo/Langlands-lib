# Moving a determinant twist between the two factors of a pair gamma factor

Author: Worker 389.

The module defines the proposition
`Langlands.RankinSelberg.PairGammaTwistExchangeStatement.{uF, uV, uW}`. It says that a gamma
certificate of the pair `(π ⊗ χ∘det, σ)` is the same as a gamma certificate of the pair
`(π, σ ⊗ χ∘det)`. It contains no proof and no axiom, and it defines no new gamma factor. It
generalizes the proved `RankOneGammaTwistStatement` (where `σ` is the trivial character of
`GL_1`) to a second factor of arbitrary rank.

## Exact scope

The proposition quantifies over:

- every prime `p` and every `F : PadicField.{uF} p`, used with its canonical topological data;
- every `ψ : UnitaryAdditiveCharacter F.Carrier` in the canonical topology;
- every `ν : AdditiveHaarMeasure F.Carrier` for the Borel structure of that topology;
- every `r t : ℕ` (both orders and equal ranks are allowed);
- complex modules `V : Type uV`, `W : Type uW` with independent universes;
- every `π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V`;
- every `σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W`;
- every group homomorphism `χ : F.Carrierˣ →* ℂˣ`;
- every `G : RationalFunctions`.

It asserts exactly the equivalence

`IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp GeneralLinear.determinant) π) σ G`

if and only if

`IsPadicSymmetricGammaFactor F ψ ν π (Langlands.twist (χ.comp GeneralLinear.determinant) σ) G`.

`Langlands.twist` (`Representation/Twist/Definitions.lean`) is the action
`g ↦ χ(det g) • π(g)` on the same module. Both sides use the same `ψ`, `ν` and `G`; for
residue cardinality `q`, `G` stands for `γ(s) = G(q^(-s))`.

`IsPadicSymmetricGammaFactor` (`RankinSelberg/PadicPairFactors.lean:171`) reads the pair in
larger-rank-first order: it is `IsPadicPairGammaFactor` of `(first, second)` when `t ≤ r`, and
of `(second, first)` when `r < t`. The rank condition is the same on both sides, so:

- when `t < r`, both sides are unequal-rank relations with candidate `π ⊗ χ` resp. `π` and test
  `σ` resp. `σ ⊗ χ` (`IsUnequalRankGammaFactor`, `RankinSelberg/GammaFactor.lean:289`);
- when `r < t`, both sides are unequal-rank relations with candidate `σ` resp. `σ ⊗ χ` and test
  `π ⊗ χ` resp. `π`;
- when `r = t`, both sides are equal-rank relations (`IsEqualRankGammaFactor`,
  `GammaFactor.lean:269`) with `π ⊗ χ` resp. `π` first, after the cast in `IsPairGammaFactor`
  (`GammaFactor.lean:309`).

Each side keeps the full content of the relation: existence of a compatible quotient
measure, existence of nonzero Whittaker functionals for the candidate and inverse Whittaker
functionals for the test, and the gamma functional equation (`UnequalRankGammaEquation`,
`GammaFactor.lean:177`, or `EqualRankGammaEquation`, `GammaFactor.lean:94`) for every
compatible quotient measure and every pair of nonzero functionals, including the minus-one
scalar `ζ` of the test model and the exponent (candidate rank minus one) on `ζ`.

### What is not assumed

No genericity, irreducibility, admissibility, smoothness or central character of `π` or `σ`,
no finite dimensionality, no continuity of `χ` and no self-duality of `ν` is assumed. The
statement transports an already given certificate in either direction; it does not assert
that a gamma factor exists.

## Original source and interpretation

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions*, Amer.
J. Math. 105 (1983), 367–464 (`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). PDF pages are one-based
and include the cover.

- Section (0.3), printed p. 376 (PDF 11): the long Weyl element `w_n`, the block element
  `w_{n,m} = diag(1_m, w_{n-m})`, and `g^ι = ᵗg⁻¹`.
- Section (2.1), printed pp. 385–386 (PDF 20–21): `W̃(g) = W(w_n g^ι)`.
- The integrals (2.4), printed p. 387 (PDF 22), and the functional equation of
  Theorem (2.7)(iii), printed p. 391 (PDF 26), with the sign `ω_{π'}(-1)^{n-1}` given by the
  central character of the member of smaller or equal rank `m` and the larger rank `n`.

The identity stated here is not a numbered theorem of that paper. It is an internal
consequence of these definitions, recorded as derived content so that the Jacquet–Shalika
stability theorem, which twists only the first factor, can be used to change the second
factor as well. The certificate form is the Library's relational way of writing
`γ(s, (π ⊗ χ) × σ, ψ) = γ(s, π × (σ ⊗ χ), ψ)`.

## Why the formula has no extra scalar

Write `n` for the candidate rank and `m ≤ n` for the test rank. Twisting by `χ∘det` does not
change Whittaker functionals, since `χ(det u) = 1` on the upper unipotent group; a model
vector of the twist is `χ(det g) W(g)`.

**Integrals.** The unequal-rank integrals evaluate the candidate at block matrices whose
determinant is `det h`, `h` the variable of the test; the equal-rank integral evaluates both
at the same `g`. So the factor `χ(det h)` can be put on either factor: the integrals of
`(π ⊗ χ, σ)` and `(π, σ ⊗ χ)` (and of `(σ, π ⊗ χ)` and `(σ ⊗ χ, π)`) coincide.

**Dual integrals.** `W̃` of a twisted model vector is `χ(det w_n) χ(det g)⁻¹ W̃(g)`. In the
unequal-rank case the candidate's dual is further translated by `w_{n,m}`, so the dual
integral with the twisted candidate is `χ(det w_n · det w_{n-m}⁻¹)` times the integral in
which `χ(det h)⁻¹` is put on the test, while the dual of the twisted test contributes
`χ(det w_m)`. Since `det w_k = (-1)^(k(k-1)/2)`, the two dual integrals differ by
`χ(-1)^(m(n-m))`.

**Signs.** If the test model has minus-one scalar `ζ`, the twisted test has `ζ χ(-1)^m`. The
equation for the twisted test carries `(ζ χ(-1)^m)^(n-1)` in place of `ζ^(n-1)`. Altogether
the two equations differ by `χ(-1)^(m(n-m) + m(n-1)) = χ(-1)^(m(2n-m-1))`, and `m(2n-m-1)` is
even since `m(m+1)` is. So the same `G` works on both sides. In the equal-rank case both dual
integrals carry `χ(det w_n) χ(det g)⁻¹` and the sign changes by `χ(-1)^(n(n-1)) = 1`.

This is the author's derivation from the definitions, explaining why no extra scalar
appears; it is not a Lean proof.

## Expected proof dependencies

A proof must work with the actual relations: the actual `weylLong` in `firstDualFunction` and
`secondDualFunction`, the actual `blockWeylAt n r hnr` in `dualUnequalRankModelIntegralAt`
(`RankinSelberg/FunctionalEquationStatement.lean`), every compatible quotient measure, every
pair of nonzero functionals, every block pair `(j, k)`, the nonzero-continuation witnesses,
the existence clauses and the `r = t` cast. Available Library tools include
`twistFunctional`/`untwistFunctional` in `Representation/Whittaker/AlgebraicTwist`,
`determinantCharacter_unipotent` in `Representation/Whittaker/Twist`, the determinant
identities in `RankinSelberg/TwistInvariance`, `HasModelMinusOneScalar.unique`, and the proof
of `RankOneGammaTwistStatement` (`RankOneGammaTwistProof.lean` and its helper modules) as a
template.
