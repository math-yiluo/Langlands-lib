# Proof that group automorphisms scale compatible quotient measures

Author: Worker 787.

`Langlands.QuotientIntegration.compatibleQuotientAutomorphismScaling` proves
exactly the published proposition
`Langlands.QuotientIntegration.CompatibleQuotientAutomorphismScaling.{uG}` from
`Langlands.Analysis.Local.QuotientAutomorphismStatement`. The theorem is
unapplied, and its type is that proposition at the same universe `uG`. This
module adds a proof and three intermediate lemmas. It changes neither the
statement pair nor any imported published pair.

## What is proved

The setting is the one of the statement, with no hypothesis added:

- `G : Type uG` is a Hausdorff locally compact topological group with a Borel
  structure;
- `H` is a closed subgroup, with a Borel structure on `H` and on the actual
  quotient `LeftQuotient H` of cosets `H * g`;
- `μG` and `μH` are arbitrary supplied measures, each `IsHaarMeasure`,
  `Regular` and `IsMulRightInvariant`;
- `ν` is any measure with the unchanged `IsCompatible H μG μH ν`;
- `α : G ≃ₜ* G` is a continuous automorphism and `hα : ∀ x, α x ∈ H ↔ x ∈ H`.

Write `αH = subgroupAutomorphism H α hα`, `αQ = quotientAutomorphism H α hα`,
`δG = mulEquivHaarChar α` and `δH = mulEquivHaarChar αH`. These are the
published restriction to `H`, the published homeomorphism `[g] ↦ [α g]` of
the quotient, and Mathlib's Haar moduli. The theorem proves both conjuncts of
the statement:

```text
Measure.map αQ ν = (((δH / δG : ℝ≥0) : ℝ≥0∞)) • ν
∀ f : LeftQuotient H → ℂ,
  (∫ q, f (αQ.symm q) ∂ν) = (((δG / δH : ℝ≥0) : ℝ) : ℂ) * ∫ q, f q ∂ν
```

The second identity is for every complex function `f`, with no measurability,
integrability or continuity premise, under Mathlib's total Bochner integral.

No countability, σ-compactness, compact-open basis, nonarchimedean,
normality, normalization, uniqueness or scaling hypothesis is used. No
uniqueness of compatible measures is assumed: the needed comparison of two
specific measures is proved inside the module, by compact-test
extensionality.

## Measure hypotheses actually used

- From `IsCompatible`, the proof uses only the fields `regular` and
  `integral_formula`. It does not use `nonzero`, `right_invariant` or
  `averaging_integrable`.
- Right invariance of `μG` is not used. Right invariance of `μH` is used only
  because the published `IsCompatible`, `quotientAverage` and
  `quotientAverageReal` take it as an instance argument.
- Regularity and the Haar property of `μG` and `μH` are used in the two Haar
  changes of variables. Local compactness of `H` comes from closedness, as
  `hH.locallyCompactSpace`, exactly as inside the statement.
- The quotient is Hausdorff by the published `leftQuotient_t2Space` (from
  closedness of `H`) and locally compact by `leftQuotient_locallyCompactSpace`.
  These are needed for compact-test extensionality.

## The intermediate lemmas

### `mulEquivHaarChar_mul_integral_comp`

For a locally compact group `K` with a regular Haar measure `μ`, a
continuous automorphism `φ : K ≃ₜ* K` and any `F : K → ℝ`,

```text
(mulEquivHaarChar φ : ℝ) * ∫ x, F (φ x) ∂μ = ∫ x, F x ∂μ.
```

This is Mathlib's `mulEquivHaarChar_smul_integral_map`, which states
`mulEquivHaarChar φ • ∫ F ∂(μ.map φ) = ∫ F ∂μ`, combined with
`integral_map_equiv` for the Borel measurable equivalence of `φ`. Neither
lemma needs integrability of `F`, so this lemma holds for every `F`.

### `IsCompatible.integral_quotientAverageReal`

For continuous compactly supported `f : G → ℝ`,

```text
(∫ q, quotientAverageReal H μH f q ∂ν) = ∫ g, f g ∂μG.
```

This is the real form of the complex Weil formula `integral_formula` of
`IsCompatible`, applied to `g ↦ (f g : ℂ)`. The published
`quotientAverage_ofReal` and Mathlib's `integral_complex_ofReal` move the
coercion outside both integrals.

### `IsCompatible.integral_comp_quotientAutomorphism`

For every `φ : C_c(LeftQuotient H, ℝ)`,

```text
(∫ q, φ (αQ q) ∂ν) = ((δH : ℝ) / (δG : ℝ)) * ∫ q, φ q ∂ν.
```

The proof has four steps.

1. **Lifting.** The published `realQuotientPositiveLifting`
   (`Langlands.Analysis.Local.QuotientPositiveLifting`) gives
   `f : C_c(G, ℝ)` with `quotientAverageReal H μH f = φ` on every coset.
   Only the lifting is used, not its positivity part.
2. **Subgroup change of variables.** On the coset `[g]`,
   `φ (αQ [g]) = φ [α g] = ∫ f (h * α g) dμH(h)`. Apply the first lemma to
   `K = H`, `φ = αH` and `F(h) = f (h * α g)`. Since
   `α h * α g = α (h * g)`, it gives

   ```text
   φ (αQ [g]) = δH * ∫ f (α (h * g)) dμH(h) = δH * quotientAverageReal H μH (f ∘ α) [g].
   ```

3. **Weil formula twice.** The function `f ∘ α` is continuous with compact
   support, because `α` is a homeomorphism. Integrating step 2 against `ν`
   and using the second lemma for `f ∘ α` and for `f` gives

   ```text
   ∫ φ ∘ αQ dν = δH * ∫ f ∘ α dμG,      ∫ φ dν = ∫ f dμG.
   ```

4. **Ambient change of variables.** The first lemma for `K = G` and `φ = α`
   gives `δG * ∫ f ∘ α dμG = ∫ f dμG`. Since `δG > 0`
   (`mulEquivHaarChar_pos`), the two lines of step 3 combine to the claimed
   factor `δH / δG`.

### `IsCompatible.map_quotientAutomorphism`

This is the first conjunct,
`Measure.map αQ ν = (((δH / δG : ℝ≥0) : ℝ≥0∞)) • ν`. Both sides are regular
measures on a locally compact Hausdorff space:

- `ν` is regular by the `regular` field of `IsCompatible`;
- `Measure.map αQ ν` is regular by Mathlib's `Measure.Regular.map`, because
  `αQ` is a homeomorphism;
- the right side is regular by `Measure.Regular.smul`, because the scalar is
  finite.

Mathlib's `Measure.ext_of_integral_eq_on_compactlySupported` (from the
Riesz–Markov–Kakutani development) says that two regular measures with the
same integral for every `φ : C_c(LeftQuotient H, ℝ)` are equal. The integral
of `φ` against `Measure.map αQ ν` is `∫ φ ∘ αQ dν`, by `integral_map_equiv`.
The integral against the scaled measure is `(δH / δG) * ∫ φ dν`, by
`integral_smul_measure`. The previous lemma says these agree.

This replaces the uniqueness argument mentioned in the statement Markdown:
the two specific measures `Measure.map αQ ν` and `(δH / δG) • ν` are compared
directly by their compact real tests. The task suggests the compact-test
extensionality used in `Langlands.Analysis.Local.QuotientFunctional`, whose
`measureOfPositiveAveraging_unique` is built on the same Mathlib theorem; this
proof calls Mathlib's theorem itself.

## The closing theorem

`compatibleQuotientAutomorphismScaling` introduces all the quantified data,
installs `LocallyCompactSpace H` from `hH.locallyCompactSpace` as the
statement does, and unfolds the local names `αH`, `αQ`, `δG`, `δH`.

The first conjunct is `IsCompatible.map_quotientAutomorphism`.

For the second conjunct, let `f : LeftQuotient H → ℂ` be arbitrary.
`integral_map_equiv` for the Borel measurable equivalence of `αQ` gives

```text
∫ f (αQ.symm q) ∂(Measure.map αQ ν) = ∫ f (αQ.symm (αQ q)) ∂ν = ∫ f q ∂ν.
```

This identity of total Bochner integrals holds for every `f`, because
`integral_map_equiv` has no measurability or integrability hypothesis.
Rewriting the left side by the first conjunct and `integral_smul_measure`
gives

```text
((δH / δG : ℝ≥0) : ℂ) * ∫ f (αQ.symm q) ∂ν = ∫ f q ∂ν.
```

Both moduli are positive (`mulEquivHaarChar_pos`), so
`(δG / δH) * (δH / δG) = 1` in `ℝ≥0`. Multiplying by `δG / δH` gives the
second conjunct. Nonintegrable `f` needs no separate case: both total
integrals are then zero, and the identities above remain true.

The axioms of the closing theorem are `propext`, `Classical.choice` and
`Quot.sound`. There are no proof holes and no new axioms.

## Reciprocal directions

The two conjuncts carry reciprocal factors. Bernstein and Zelevinsky define
the module of an automorphism `σ` by the inverse-integrand identity
`∫ f(σ⁻¹ u) dμ(u) = mod(σ) ∫ f dμ`, the same convention as Mathlib's
`mulEquivHaarChar` (`mulEquivHaarChar φ • μ.map φ = μ`). Thus

- the forward pushforward `Measure.map αQ ν` is `ν` scaled by `δH / δG`;
- the inverse-integrand form, which is the source's definition of the
  quotient module, has the factor `δG / δH`. This matches the source's
  `mod_{U'\U} = mod_U / mod_{U'}` with `U = G` and `U' = H`.

In the proof, the factor `δH / δG` is the primary computation (third lemma),
and `δG / δH` is obtained from it by inverting the positive ratio.

## Provenance

This is an internal formalization. The proof route is derived for the
project's quotient conventions and is not a transcription of a source proof.

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups. I*, Ann. Sci. École Norm. Sup.
(4) 10 (1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`
(SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).

- **Section 1.7** (printed pp. 443–444) defines `mod_U σ` by the
  inverse-integrand identity. On p. 444 it remarks, without a numbered
  theorem or a proof beyond one sentence, that for unimodular `U' ⊂ U` closed
  and `σ(U') = U'`, "The Fubini theorem implies that
  `mod_{U'\U} = mod_U/mod_{U'}`." The present module proves a general locally
  compact version of this remark, for every compatible quotient measure. Its
  proof uses the Weil formula of `IsCompatible` in place of Fubini's theorem.
- **Section 5.17** (printed pp. 466–467) is Case IV₂ of the proof of
  Theorem 5.2: §5.16 divides Case IV into IV₁ and IV₂. There the authors
  choose a Haar measure on `V'\V` "(see 1.7)" and, for `n ∈ N`, make the
  replacement `v = n⁻¹ ṽ n` in an integral over `V'\V`, which "according to
  1.7" produces the factor `mod_{V'\V}(n)`. This theorem is an analytic
  prerequisite for that conjugation calculation. It does not identify the
  module with a determinant of the unipotent action. It also does not prove
  the algebraic equivariance of compact induction or the full normalized
  orbit comparison, which belong to later work by Worker 76
  (`Langlands.Geometric.PadicParabolicOrbitJacquetComparison`).

No erratum for this source was found among the project notes of the current
Library.
