# Proof of the equal-rank rank-one extension Laurent-span comparison

Author: Worker 719.

This module proves the published proposition
`Langlands.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement.{uF,uV,uW}`
from `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement`.
The final theorem is

```lean
theorem Langlands.RankinSelberg.equalRankRankOneExtensionSpanComparison :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW}
```

It is obtained through two intermediate conditional theorems, which are
also proved in this module:

```lean
theorem Langlands.RankinSelberg.equalRankRankOneExtensionSpanComparison_of
    (h91 : Whittaker.TwoBlockWhittakerExtensionStatement.{uF, 0, uW}) :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW}

theorem Langlands.RankinSelberg.equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity
    (hsurj : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (d : ℕ),
      HarmonicAnalysis.PadicRowFourierSurjectivityStatement F F.canonicalTopologicalData d) :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW}
```

The first hypothesis is the published statement of JPSS Proposition 9.1
(`Langlands.Whittaker.TwoBlockWhittakerExtensionStatement`, used at the
first-block universe `0`). The second theorem discharges it with the published
conditional proof
`Langlands.Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity`
(module `Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof`).
Its only premise is p-adic row Fourier surjectivity for the canonical
topology. The final theorem supplies that premise from the published theorem
`Langlands.HarmonicAnalysis.padicRowFourierSurjectivity`
(module `Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof`),
specialized to `F.canonicalTopologicalData`. The equal-rank last-row
reduction is the published theorem
`Langlands.RankinSelberg.equalRankLastRowReduction` from
`Langlands.Representation.RankinSelberg.EqualRankLastRowReductionProof`. The
module uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Character change

`standardCharacter_scale_neg_one ψ n` says that the standard character of
`ψ.scale (-1)` (that is, `ψ⁻¹`) is the inverse standard character of `ψ`. The
equation is propositional, so Whittaker sets for the two characters are
related by a transport lemma.

- `exists_mem_coefficientModel_of_character_eq`: if `θ = θ'`, a coefficient
  function in the model of a `θ`-functional is also in the model of some
  `θ'`-functional, with the same underlying function.
- `exists_inverseWhittakerSet_of_scale_neg_one`: every `W` in
  `whittakerSet (ψ.scale (-1)) n π` has the same values as some member of
  `inverseWhittakerSet ψ n π`.
- `exists_whittakerSet_scale_neg_one`: the converse direction.

## Restriction to `diag(h, 1)`

`corankOneRestrict ψ W'` is the function `h ↦ W'(rankInclusion 1 h)` for an
inverse Whittaker function `W'` of rank `n + 2`, with the proof that it is an
inverse Whittaker function of rank `n + 1`. The proof uses the published
`corankOne_standardCharacter`. Its value lemma `corankOneRestrict_val` holds
by `rfl`.

## Block `j = k = 0` convergence

- `prod_dirac_eq_map`: `μ.prod (dirac y) = μ.map (x ↦ (x, y))` for an
  arbitrary measure `μ`. Mathlib's `Measure.prod_dirac` needs `SFinite μ`;
  this version follows from `Measure.prod_def`, `Measure.map_dirac'` and
  `Measure.bind_dirac_eq_map`.
- `corankOneConverges_of_unequalRankConverges_zero_zero`: block convergence
  `UnequalRankConverges … 0 0 μ (dirac 0) W W' s` implies
  `CorankOneConverges … μ W W' s`. Compose integrability over the product
  with the measurable map `x ↦ (x, 0)` and use the published
  `unequalRankIntegrand_zero_zero`.

## Span inclusion from constant multiples

The imported `zetaSpan_le_of_forall_exists_const_mul` from
[`RankOneExtensionSpanTransfer`](RankOneExtensionSpanTransfer.md) says that if
for every `R ∈ S` some nonzero `c : ℂ` has `RatFunc.C c * R ∈ T`, then
`zetaSpan S ≤ zetaSpan T`. Its proof multiplies by the Laurent constant `c⁻¹`,
using `algebraMap_laurent` and `laurentToRatFunc_C`.

## Weight identity

`half_mul_determinantWeight`:
`|det g|^(1/2) · |det g|^(s - 1/2 - 1/2) = |det g|^(s - 1/2)` for the normalized
absolute value of a p-adic field. The absolute value of `det g` is positive
because `g` is invertible, so complex powers add (`Complex.cpow_add`).

## Transport of the induced representation

- `reindex_finCongr_self`: reindexing along `finCongr` of `k = k` is the
  identity (simp lemma), imported from `Langlands.Group.GL.ReindexCongr` under
  the unchanged `Langlands.RankinSelberg` name.
- `pairFamilyEquivRight ρ₁ e`: from an equivalence `e : ρ₂ ≃ ρ₂'`, the
  blockwise equivalences `pairFamily ρ₁ ρ₂ i ≃ pairFamily ρ₁ ρ₂' i`
  (identity on block `0`, `e` on block `1`).
- `conjULiftEquiv ρ`: `ρ` is equivalent to its conjugate by
  `ULift.moduleEquiv.symm` on `ULift.{uV'}` of its carrier. The underlying
  linear equivalence is `ULift.moduleEquiv.symm`, and equivariance holds by
  `rfl`.

## Proposition 9.1 with a rank-one first block

`exists_inverseWhittaker_twoBlockExtension h91 F ψ t σ₁ χ hσ` states: for every
`W₁ ∈ inverseWhittakerSet ψ t σ₁` and every Schwartz–Bruhat `Φ₀` on
`F^(t+1)`, there is `W'` in the inverse Whittaker set of rank `1 + t` of
`I = canonicalNormalizedProductInduced (twoBlocks 1 (t+1) …) (pairFamily χlift σ₁)`
such that, for all `g ∈ GL_(t+1)`,

`W'(reindex (finCongr _) (rankInclusion 1 g)) = W₁(g) · Φ₀(lastRow g) · |det g|^(1/2)`.

Proof. Apply `h91` with the character `ψ.scale (-1)`, `a = 0`, `b = t`, first
block `rankOneCharacter χ` on `ℂ`, and second block `σ₁`.

- The first block is of Whittaker type for `ψ.scale (-1)` by
  `rankOneCharacter_isOfWhittakerType`.
- `σ₁` is of Whittaker type for `standardCharacter (ψ.scale (-1)) t`. Rewrite
  with `standardCharacter_scale_neg_one` and use
  `isOfWhittakerType_standard_iff_inverse`.
- The tail function is the `ψ.scale (-1)`-Whittaker function with the values
  of `W₁` (character change above).

Proposition 9.1 returns a `ψ.scale (-1)`-Whittaker function `Wξ` of the
induction `ξ` of the universe-lifted blocks. Its values on
`e (appendIdentity t 1 g)` are `W₁(g) Φ₀(lastRow g) |det g|^((0+1)/2)`. The
character change makes it an inverse `ψ`-Whittaker function. The published
`inverseWhittakerSet_eq_of_equiv` then moves it to `I`, along the equivalence
`ξ ≃ I` given by `normalizedProductInducedEquiv` with blockwise equivalences
`pairFamilyEquivRight _ (conjULiftEquiv σ₁)`. The first lifted block of `ξ` is
literally `χlift`, so block `0` is the identity there. The evaluation point
`e (appendIdentity t 1 g)` is `reindex (finCongr _) (rankInclusion 1 g)`
definitionally, and `norm_num` normalizes the exponent `(0+1)/2` to `1/2`.

## Core comparison at a general induced rank

`equalRankSpanComparison_core` proves the span inclusion for a general induced
rank `m` with `hm : t + 1 = m` and any smooth representation `I` of
`GL_(m+1)`. It assumes:

- `hC : EqualRankLastRowReductionStatement F F.canonicalTopologicalData t`;
- smoothness of `π` and `I`;
- an extension hypothesis `hext` with exactly the conclusion of
  `exists_inverseWhittaker_twoBlockExtension`, with `m` in place of `1 + t`.

The proof first substitutes `hm`, so that `hm ▸ π` is `π`. It then installs
the canonical topology, valuative relation, local-field structure and Borel
σ-algebras, matching the statement's instances. By `zetaSpan_le_of_forall_exists_const_mul`
it suffices, for each base value `R`, to find `c ≠ 0` with `c · R` an induced
value. Let `R` be given by `W ∈ whittakerSet ψ (t+1) π` (functional `ℓ`),
`W₁ ∈ inverseWhittakerSet ψ t σ₁`, a half-plane bound `a`, and the rational
continuation.

1. Cutoff. The published `zeroRowLastRowCutoff` (rank `t`, `k = 0`) gives
   `Φ₀` with `W(rankInclusion 1 g) · Φ₀(lastRow g) = W(rankInclusion 1 g)`
   for all `g ∈ GL_(t+1)`.
2. Extension. `hext W₁ Φ₀` gives `W'` in the inverse Whittaker set of `I` with
   `W'(rankInclusion 1 g) = W₁(g) Φ₀(lastRow g) |det g|^(1/2)`, after
   `reindex_finCongr_self`.
3. Stabilizer. `Whittaker.exists_compactOpen_glCoefficientRightStabilizer`
   gives a compact open subgroup `J` of `GL_(t+2)` under which both `W` and
   `W'` are right invariant.
4. Last-row indicator. `lastRowCompactOrbit` gives a Schwartz–Bruhat `Φ`
   equal to the indicator of `lastRow '' J`.
5. Reduction. `hC` with `μind`, `μbase` and `J` gives `c > 0`. Applied to
   `W`, `W'`, `W'' = corankOneRestrict ψ W'` and `Φ`, it gives, for every `s`,
   equivalent convergence and
   `equalRankIntegral μind W W' Φ s = c · corankOneIntegral μbase W W'' (s - 1/2)`.
6. Integrand identity. For every `s`, the corank-one integrand of
   `(W, W'')` at `s - 1/2` equals the corank-one integrand of `(W, W₁)` at
   `s`. On a class of `g` it is
   `W(diag(g,1)) · W₁(g) Φ₀(lastRow g) |det g|^(1/2) · |det g|^(s - 1/2 - 1/2)`.
   The cutoff removes `Φ₀`, and `half_mul_determinantWeight` combines the
   powers.

The witness for `c · R` is `(W, W', Φ)` with the same half-plane bound `a`.

- Convergence. For `Re s > a`, block convergence of `(W, W₁)` holds. The
  published `rectangularMeasure_zero_rows` turns the rectangular measure into
  `dirac 0`, and the block lemma above gives corank-one convergence. The
  integrand identity and step 5 then give equal-rank convergence.
- Continuation. By step 5 and the integrand identity, the equal-rank integral
  is `c` times the corank-one integral of `(W, W₁)`. The published
  `unequalRankIntegral_zero_zero` makes that the base block integral. The
  published `hasRationalContinuation_const_mul` gives the continuation
  `RatFunc.C c * R`.

## Final theorem

`equalRankRankOneExtensionSpanComparison_of` introduces the statement's
data and applies the core lemma with:

- `m = 1 + t` and `hm = hrn`;
- `I` the induced representation of the statement;
- `equalRankLastRowReduction F F.canonicalTopologicalData t` for `hC`;
- smoothness of `π` from its Whittaker type (`hπ.1.1`);
- smoothness of `I` from `isSmooth_normalizedProductInduced`;
- `hext` from `exists_inverseWhittaker_twoBlockExtension h91`.

`equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity` applies
`equalRankRankOneExtensionSpanComparison_of` to
`Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity.{uF, 0, uW} hsurj`.

`equalRankRankOneExtensionSpanComparison` applies the previous theorem to
`fun _ _ F d => HarmonicAnalysis.padicRowFourierSurjectivity F F.canonicalTopologicalData d`.

## Relation to the source

The route follows the derivation recorded in the statement Markdown. It
combines JPSS (1983) Proposition 9.1 (printed pages 452–454) with the last-row
reduction of printed page 449, displays (1) and (3). The extension, cutoff,
stabilizer and indicator steps are the Library's formal versions of these
steps. The constant `c` is not identified.
