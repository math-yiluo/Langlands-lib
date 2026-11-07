# Gamma factors of pairs of segment heads as epsilon-times-L-ratio expressions

Author: Worker 1695.

This module shows that a pair of segment heads `(π, σ)` has an epsilon monomial
`e`, an L-polynomial `P` and a polynomial `D` with `D(0) = 1` such that
`rationalGammaExpression δ e P D` is the product of the gamma factors of the
twisted supercuspidal pairs `(ν^(i+j) A, A')`. The only hypothesis is the
published, unproved segment-head gamma formula
`RankinSelberg.SegmentHeadGammaFactorStatement` (Henniart 2002, §2.6, third
display). Here `δ = LocalFactor.residueReflection F = q⁻¹`. Only the standard
axioms are used.

All declarations are in the namespace `Langlands.RankinSelberg`.

## Genericity

- `isGeneric_of_isPadicSymmetricGammaFactor_self`: let `π` be an irreducible
  admissible representation of `GL_(r+1)(F)` with an equal-rank gamma factor
  against itself (`IsPadicSymmetricGammaFactor F ψ ν π π G`). Then `π` is generic
  for `ψ`. The nonzero Whittaker functional is the second component of
  `isPairGammaFactor_self`. This mirrors the published epsilon version
  `isGeneric_of_isPadicSymmetricEpsilonFactor_self`.

## Constructed data for generic pairs

- `exists_isPadicSymmetricGammaFactor_rationalGammaExpression`: let `π`, `σ` be
  generic and `ν` a self-dual measure for `ψ`. Then there are `e`, `P`, `D` with:
  - `IsPadicSymmetricEpsilonFactor F ψ ν π σ e`;
  - `IsPadicSymmetricLPolynomial F ψ ν π σ P`;
  - `D.coeff 0 = 1`;
  - `IsPadicSymmetricGammaFactor F ψ ν π σ (rationalGammaExpression δ e.1 e.2 P D)`.

  The witnesses are the published `genericSymmetricEpsilonData`,
  `genericSymmetricLPolynomial` and `genericSymmetricDualLPolynomial`. The latter
  is the L-polynomial of the inverse-transpose pair at `ψ.scale (-1)` and has
  constant term `1`. The gamma relation is the published (proved)
  `symmetricGammaExpression`, with `genericSymmetricGammaConstructionInput`.
- `exists_isPadicRankGammaFactor_rationalGammaExpression`: the same statement
  for the arbitrary-rank wrappers `IsPadicRankEpsilonFactor`,
  `IsPadicRankLPolynomial` and `IsPadicRankGammaFactor`, for irreducible
  admissible `π`, `σ` with self-gamma factors. Rank zero is excluded because the
  rank-zero wrappers are `False`.

## Segment heads

- `isIrreducible_isAdmissible_of_isSegmentHead`: a segment head is irreducible
  (first component of `IsIrreducibleHead`). It is admissible because it is a
  quotient of the segment induction of an admissible supercuspidal
  representative (`SegmentFullJacquet.isAdmissible_of_segmentQuotient`).
- `exists_segmentHead_rationalGammaExpression hG ψ ν Δ Δ' π σ A A' ...`: take
  `hG : SegmentHeadGammaFactorStatement.{uF, uV, uV}`, segment heads `π` of `Δ`
  and `σ` of `Δ'`, and supercuspidal representatives `A`, `A'` of their bases.
  Then there are `e`, `P`, `D` and `H : Fin Δ.length → Fin Δ'.length → RatFunc ℂ`
  with:
  - `IsPadicRankEpsilonFactor F ψ ν π σ e`;
  - `IsPadicRankLPolynomial F ψ ν π σ P`;
  - `D.coeff 0 = 1`;
  - `IsPadicRankGammaFactor F ψ ν (ν^(i+j) A) A' (H i j)` for all `i`, `j`,
    where `ν^(i+j) A = realPowerTwist (determinantNorm Δ.rank) (i + j) A`;
  - `rationalGammaExpression δ e.1 e.2 P D = ∏ i, ∏ j, H i j`.

  The proof applies `hG` three times:
  - to `(Δ, Δ)`, which gives a self-gamma factor of `π` and hence genericity;
  - to `(Δ', Δ')`, likewise for `σ`;
  - to `(Δ, Δ')`, which gives the product formula.

  Gamma-factor uniqueness then identifies the two expressions.

## Provenance

Henniart 2002 (`henniart-2002-characterization`), §2.6, printed page 595, third
display, enters only through the published hypothesis
`SegmentHeadGammaFactorStatement`. The remaining steps combine published proved
results (genericity criteria, constructed JPSS data, `symmetricGammaExpression`,
admissibility of segment quotients).
