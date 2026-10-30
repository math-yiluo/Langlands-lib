# Proof of the rank-one JPSS comparison `I₁ = I₃`

Module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof`.
It proves the published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement.{uF,uV}`, unchanged,
as

```text
theorem Langlands.RankinSelberg.rankOneMatrixWhittakerComparison :
    RankOneMatrixWhittakerComparisonStatement.{uF, uV}
```

The statement covers every prime `p`, every canonical `p`-adic field `F`, every
bundled nontrivial unitary additive character `ψ`, every `n` (including `n = 0`),
and every complex representation `σ` of `GL(n + 1)` on an arbitrary carrier with
`IsOfWhittakerType`. It also covers every nonzero standard functional `ℓ` and every
compatible rank-one quotient measure `μ`. The conclusion is the equality of
Laurent submodules

```text
zetaSpan (characterZetaValues q ψ abv μ 1 n σ) = GodementJacquet.Padic.jpssI3 F ψ σ ℓ.
```

The proof adds no hypotheses. It uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). This module only assembles the result; the
mathematics is in the helper modules listed below.

## Assembly

- `rankOneMatrixWhittakerComparison_of_positive` derives the statement from a
  positive-rank identification `hpos`. It splits on `n`.
  - `n = 0`: this is `rankOneMatrixWhittakerComparison_zero` (module
    `RankOneMatrixWhittakerComparisonZero`). It is the actual `GL₁` equal-rank
    (Tate) bridge. It uses the triviality of `N₁`, the uniqueness of the compatible
    quotient measure, the constant inverse Whittaker functions of the trivial
    character, the correspondence of vector and `1 × 1` matrix tests, and the zero
    shift.
  - `n = m + 1`: the canonical topology, valuation, local-field structure and the
    Borel structures needed by the published definitions are reinstated. Then
    `characterZetaValues_one_succ_eq` (module `RankOneMatrixWhittakerComparisonLeft`)
    rewrites the left value set as the reduced set
    `rankOneModelValues q ψ abv (generalLinearHaar F 0) σ ℓ`. This step uses the
    identity rank relabelling `characterPairRank`, the zero-row rectangular
    variable and the constant inverse Whittaker functions of `GL₁`. It also uses
    `IsOfWhittakerType` to identify the all-functional `whittakerSet` with the
    coefficient model of the specified `ℓ`, since the functional space is a line.
    Finally `hpos` rewrites the right side, and `congrArg zetaSpan` concludes.
- `whittakerRationalValues_eq_rankOneModelValues` is `hpos`. For smooth `σ` on
  `GL(m + 1 + 1)` and every `ℓ`,

  ```text
  GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ
    = rankOneModelValues F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier 0) σ ℓ.
  ```

  It is `Set.Subset.antisymm` of two inclusions.
  - `RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues` (module
    `RankOneMatrixWhittakerComparisonExpansion`, by Worker 901). Every matrix
    integral `Z(Φ, s + (m+1)/2, W)` equals a rank-one integral `Ψ(s, W')`, for one
    model function `W'` and every `s` in the convergence region. The proof uses
    Iwasawa unfolding, a finite level-set expansion and a Fourier cutoff.
  - `rankOneModelValues_subset_whittakerRationalValues` (module
    `RankOneMatrixWhittakerComparisonBox`, by Worker 902). For one explicit compact
    open box `Φ₀` and one constant `C > 0`, `Z(Φ₀, s + (m+1)/2, W) = C · Ψ(s, W)`
    whenever `Ψ(s, W)` converges absolutely, with absolute convergence of the
    matrix integral.

  Both inclusions transfer absolute convergence on a right half-plane and the
  rational continuation in `q^(-s)`. The exponent is `s - (m+1)/2` on the
  character side and `s + (m+1)/2` on the matrix side, with `(m+1)/2` complex. The
  smoothness hypothesis comes from `IsOfWhittakerType` (admissibility contains
  smoothness).

## Helper modules

All are new paired modules of this proof.

- `RankOneMatrixWhittakerComparisonZero`: the `n = 0` branch, and two shared lemmas
  (`whittakerSet` versus the coefficient model; constant inverse Whittaker
  functions at rank one).
- `RankOneMatrixWhittakerComparisonValues`: the definitions `rankOneEmbedding`,
  `rankOneModelIntegrand` and `rankOneModelValues`.
- `RankOneMatrixWhittakerComparisonLeft`: the left side at positive rank.
- `RankOneMatrixWhittakerComparisonCutoff`: multiplying a model function on the
  embedded `GL₁` by a Schwartz–Bruhat function of `det g`.
- `RankOneMatrixWhittakerComparisonSupport`: the support bound
  `W(diag(det g, 1, …, 1)) ≠ 0 → det g ∈ π^(-a) O`.
- `RankOneMatrixWhittakerComparisonLevelSets`: product integrals of families with
  finitely many values.
- `RankOneMatrixIwasawa`: Iwasawa integration on `GL(n + 1)` with constant one.
- `RankOneMatrixUnipotentIntegral`: the unipotent transform, lattice bounds and
  congruence subgroups.
- `RankOneMatrixUnfolding`: unfolding the matrix integral over `N`.
- `RankOneMatrixWhittakerComparisonExpansion`: the inclusion of the matrix values
  in the reduced values.
- `RankOneMatrixWhittakerComparisonBox`: the reverse inclusion.

## Scope and provenance

The positive-rank route follows Jacquet, Piatetski-Shapiro and Shalika,
*Automorphic forms on GL(3) I* (1979), Section 4: Remark (4.2), Theorem (4.3), and
Lemmas (4.3.1) and (4.3.4) with the proof of (4.3) (printed pp. 188–194). JPSS
(1983), Section 5.2 (printed pp. 420–421) invokes this result for `I₁ = I₃`. The
implemented arguments are internal variants and are described in the helper
Markdown files.

Only smoothness of the representation enters the positive-rank analysis.
Admissibility, finite generation over the group algebra and irreducibility of the
coefficient model are not needed, so the proof neither assumes nor proves them.
The multiplicity-one part of `IsOfWhittakerType` is used only to identify the
`whittakerSet` on the left with the specified model. The proof does not use
product commutativity, uniqueness of factors, functional equations, two-block
multiplicativity, or the matrix-model `I₂ = I₃` comparison.
