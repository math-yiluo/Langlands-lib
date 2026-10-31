# Rank-one determinant twists of gamma certificates

Author: Worker 1062.

The module defines the proposition
`Langlands.RankinSelberg.RankOneGammaTwistStatement.{uF, uV}`.
It says that a gamma certificate can be moved between two pairs: the
determinant twist of a representation paired with the trivial rank-one
character, and the untwisted representation paired with the rank-one
character itself. The module contains no proof and no axiom. It defines no
new gamma factor and changes no existing definition.

## Exact scope

The proposition quantifies over:

- every prime `p`;
- every `F : PadicField.{uF} p`, used with its canonical topological data;
- every `ψ : UnitaryAdditiveCharacter F.Carrier` in the canonical topology;
- every supplied `ν : AdditiveHaarMeasure F.Carrier` for the Borel structure
  of that topology;
- every `n : ℕ`, including `n = 0`;
- every complex module `V : Type uV`, whose universe is independent of `uF`;
- every `π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V`;
- every group homomorphism `χ : F.Carrierˣ →* ℂˣ`;
- every `G : RationalFunctions`.

Under these quantifiers it asserts exactly the equivalence

`IsPadicSymmetricGammaFactor F ψ ν (Langlands.twist (χ.comp GeneralLinear.determinant) π) (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G`

if and only if

`IsPadicSymmetricGammaFactor F ψ ν π (rankOneCharacter χ) G`.

Here `Langlands.twist` (`Representation/Twist/Definitions.lean:19`) is the
action `g ↦ χ(det g) • π(g)` on the same module `V`. The rank-one character
`rankOneCharacter η` (`RankinSelberg/LocalFactor.lean:439`) is the existing
`characterRepresentation (η.comp determinant)` on `ℂ`. For `η = 1` it is the
trivial one-dimensional representation of `GL_1(F)`. Both sides use the same
`ψ`, the same `ν` and the same `G`. For residue cardinality `q`, `G` stands
for `γ(s) = G(q^(-s))` in the existing relation.

### How the existing relation unfolds

`IsPadicSymmetricGammaFactor` (`RankinSelberg/PadicPairFactors.lean:171`)
puts the pair in the larger-rank-first order. The test has rank one and the
candidate has rank `n + 1`. So its condition `0 ≤ n` always holds, and both
sides are `IsPadicPairGammaFactor` (`RankinSelberg/GammaFactor.lean:451`)
with the candidate first. That relation uses the canonical topology, the
Borel structures, the residue cardinality and the normalized absolute value
of `F`. It is then `IsPairGammaFactor` (`GammaFactor.lean:309`):

- When `n > 0`, it is `IsUnequalRankGammaFactor` (`GammaFactor.lean:289`)
  with `0 < n`.
- When `n = 0`, it is `IsEqualRankGammaFactor` (`GammaFactor.lean:269`),
  applied after the cast `hrn ▸ π` along `n = 0`.

Each side keeps all of the following, unchanged:

- existence of a compatible quotient measure;
- existence of a nonzero Whittaker functional for the candidate;
- existence of a nonzero inverse Whittaker functional for the test;
- a universal quantifier over every compatible quotient measure `μ`;
- a universal quantifier over every pair of nonzero functionals `ℓ, ℓ'`.

For each such choice, the equation keeps its own content. In
`UnequalRankGammaEquation` (`GammaFactor.lean:177`) this is:

- a model minus-one scalar `ζ` of the test with `HasModelMinusOneScalar`
  (`RankinSelberg/FunctionalEquationStatement.lean:94`);
- for every block decomposition `n = 0 + (j + k + 1)`, a nonzero rational
  continuation in the block-`j` family;
- for every pair of model vectors, continuations `R` of the block-`j`
  integral and `Rdual` of the transformed block-`k` integral
  `dualUnequalRankModelIntegralAt` (`FunctionalEquationStatement.lean:226`),
  related by `GammaFunctionalEquation` (`GammaFactor.lean:27`) with factor
  `ζ^n`.

In `EqualRankGammaEquation` (`GammaFactor.lean:94`) for `n = 0` it is:

- a model minus-one scalar `ζ` of the test;
- a nonzero continuation;
- for every pair of model vectors and every Schwartz–Bruhat function `Φ`, a
  Fourier partner of `Φ` with respect to `ψ` and `ν`, and continuations `R`
  and `Rdual` related with factor `ζ^0`.

`ν` enters through the rectangular measures of both blocks and through the
row Fourier transform. The statement does not replace either side by an
equation for one fixed measure or one fixed pair of functionals.

### What is not assumed or asserted

The only hypotheses are those carried by the types of the bound variables.
`UnitaryAdditiveCharacter` includes continuity and nontriviality by its
structure (`HarmonicAnalysis/Basic.lean:20`). `AdditiveHaarMeasure` includes
the Haar and regularity conditions (`HarmonicAnalysis/Basic.lean:94`). No
further premise is added. In particular, none of the following is assumed:

- irreducibility, Whittaker type, admissibility or smoothness of `π`;
- finite dimensionality of `V`;
- continuity of `χ`;
- a central character on the original carrier `V`;
- self-duality of `ν` with respect to `ψ`.

The statement transports an already given certificate in either direction.
It does not assert that any gamma factor exists. It makes no analytic
comparison between matrix-coefficient and Whittaker integrals.

## Original source and interpretation

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained PDF is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
PDF page numbers below are one-based and include the cover. No project errata
file for this source was present when this was written.

The definitions used here come from that paper:

- Section (0.3), printed page 376 (PDF 11), gives:
  - the long Weyl element `w_r`, with `w_1 = 1`;
  - the block element `w_{r,t} = diag(1_t, w_{r-t})`;
  - the involution `g^ι = ᵗg⁻¹`.
- Section (2.1), printed pages 385–386 (PDF 20–21), gives:
  - the representation `π^ι`;
  - the dual function `W̃(g) = W(w_r g^ι)`;
  - for rank one, the Whittaker model of a character, which is the line
    spanned by that character.
- The integrals (2.4), printed page 387 (PDF 22), and the functional
  equation of Theorem (2.7)(iii), printed page 391 (PDF 26), give the rest.
  That functional equation:
  - uses the right translate of `W̃` by `w_{r,t}`;
  - pairs block `j` with block `k`;
  - has the sign `ω_{π'}(-1)^{r-1}` from the central character of the
    member `π'` of smaller or equal rank.

  The source writes this equation with the epsilon factor and quotients by
  L-factors. The Library's gamma equation states the same relation with one
  rational function `G` in place of the epsilon factor times the L-ratio.

In the Library these are `weylLong` (`Group/GL/Maps.lean:63`), `blockWeylAt`
(`FunctionalEquationStatement.lean:80`), `firstDualFunction` and
`secondDualFunction` (`FunctionalEquationStatement.lean:41`, `:48`), and the
gamma equations described above. The Library's minus-one scalar `ζ` of the
test model plays the role of `ω_{π'}(-1)`. The exponent `n` is the source's
`r - 1` for candidate rank `r = n + 1`.

The twist identity stated here is not a numbered theorem of that paper. It is
an internal consequence of the integral and dual-transform definitions above.
It is derived and stated here so that a trivial rank-one test can be replaced
by an arbitrary character `χ`. The certificate form is the Library's
relational way of writing `γ(s, (π ⊗ χ∘det) × 1, ψ) = γ(s, π × χ, ψ)`.

## Why the formula has no extra scalar

Take the same nonzero functional `ℓ` on both sides. This works because
`χ(det u) = 1` on the upper unipotent group, so `π` and its twist have the
same Whittaker functionals. Then every model vector of the twist has the form
`f(g) = χ(det g) f₀(g)`, where `f₀` is the corresponding model vector of `π`.
The group `GL_1` has trivial unipotent radical, so every linear functional on
`ℂ` is a test functional. Its model is spanned by the rank-one character:
the constant `1` on the twisted side, and `χ` on the original side.

**Integrals.** The block matrix in the unequal-rank integral has the
determinant of its `GL_1` corner `h`. The factor `χ(det h)` that comes from
`f` is therefore the same as the value at `h` of the test model vector `χ`
on the original side. So the two families of integrals at `s` coincide. The
same holds in the equal-rank case `n = 0`.

**Dual integrals, `n > 0`.** For the candidate, the dual function evaluates
at `w_(n+1) · g^ι`, and the dual integral then translates on the right by
`blockWeylAt 0 n = diag(1, w_n)`. Twisting therefore multiplies it by

`χ(det w_(n+1)) · χ(det w_n)⁻¹ · χ(det g)⁻¹`.

Since `det w_m = (-1)^(m(m-1)/2)`, the ratio `det w_(n+1) / det w_n` equals
`(-1)^n`. The rank-one dual of the test sends `χ` to `χ⁻¹`, because
`w_1 = 1`. So the twisted dual integral is `χ((-1)^n)` times the original
dual integral.

**Comparing the two equations.** Write `R` and `Rdual` for the
continuations on the original side. The minus-one scalar of the trivial test
is `1`, so the twisted equation reads `χ(-1)^n · Rdual = 1^n · G · R`. The
minus-one scalar of the test `χ` is `χ(-1)`, so the original equation reads
`Rdual = χ(-1)^n · G · R`. Since `χ(-1)^2 = χ(1) = 1`, multiplying either
equation by `χ(-1)^n` gives the other. Hence the same `G` works on both
sides.

**`n = 0`.** The gamma equation has central exponent `0`, `w_1 = 1`, and the
dual integrals coincide after the same identification.

This is the author's derivation from the definitions. It explains why the
target has the same `G` on both sides, but it is not a Lean proof.

## Expected proof dependencies

A proof must work with the actual relations. In particular, it must use the
actual `weylLong (n + 1)` in `firstDualFunction` and the actual
`blockWeylAt 0 n` in `dualUnequalRankModelIntegralAt`, and compute the
resulting determinant scalar. It must not assume that the dual integrals are
unchanged by the twist. It must handle every compatible quotient measure,
every pair of nonzero functionals, every block pair `(j, k)`, the
nonzero-continuation witnesses and the existence clauses on both sides. It
must also handle the `n = 0` branch through the cast in `IsPairGammaFactor`.

Available Library tools include:

- `twistFunctional`, `untwistFunctional`, `twistFunctionalEquiv` and
  `twistFunction_coefficient` in `Representation/Whittaker/AlgebraicTwist`,
  with `determinantCharacter_unipotent` in `Representation/Whittaker/Twist`;
- the determinant identities in `RankinSelberg/TwistInvariance`, for example
  `determinant_unequalRankMatrix`, and `twist_rankOneCharacter`;
- `HasModelMinusOneScalar.unique`.

The determinant of `weylLong` is not currently a named Library lemma. The
`TwistInvariance` results concern L-polynomials, not gamma equations. No
later multiplicativity result may be used for this base case. This module
imports only `PadicPairFactors` and `Twist/Definitions`, and assumes none of
these proof steps.
