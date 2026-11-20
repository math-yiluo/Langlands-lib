# Rapidly decreasing Mellin pairs for the real pair factors

Module of an intermediate result of Task 7400 (entry module `ArchimedeanRealPairIdentity`), towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`). Helper modules: `ArchimedeanInverseMellin`
(inverse Mellin transform) and `ArchimedeanGammaBounds` (Gamma factors in vertical strips).

The module constructs, for the Library's real pair `L`- and `ε`-factors, a pair `(h, k)` of
rapidly decreasing functions on `(0, ∞)` whose Mellin transforms satisfy the factor identity.
This is the pair input of `MellinPairContinuationStatement` (module `ArchimedeanMellinPair`):
it supplies that statement's nonvanishing hypothesis and its factor-identity hypothesis. It is
the analogue, for the Library's factors, of Jacquet's `(σ, ψ)` pairs.

Notation: `mellin f s = ∫₀^∞ t^(s-1) f(t) dt` (Mathlib); `RapidDecay h` means that for every
real `M` there is `C` with `‖h t‖ ≤ C t^M` for all `t > 0`.

## The statement

`Langlands.Global.RankinSelbergGlobal.RealPairMellinFactorStatement : Prop` says the following.
Let `ds, es, dds, ees : List RealBlock`, `b : ℝˣ`, `c : NNReal` with `0 < c`, and `sign : ℂ`
with `sign ≠ 0`. Write:
- `L(s) = ((realPairLFactor ds es).denominator s)⁻¹`;
- `Ld(s) = ((realPairLFactor dds ees).denominator s)⁻¹`;
- `ε(s) = realPairEpsilon ds es b c hc s` (coerced to `ℂ`).

Then there are `σ₁ : ℝ` and `h, k : ℝ → ℂ` such that:
1. `h` and `k` are measurable and `RapidDecay h`, `RapidDecay k`;
2. explicitly, for every `s : ℂ`, with `D = (realPairLFactor ds es).denominator` and
   `Dd = (realPairLFactor dds ees).denominator`:
   - `mellin h (-s) = sign · ε(s) · exp(s²) · D(s)`;
   - `mellin k (s - 1) = exp(s²) · Dd(1 - s)`;
3. `mellin h (-s) ≠ 0` and `mellin k (-s) ≠ 0` whenever `σ₁ < Re s`;
4. for `s` outside a discrete closed subset of `ℂ` (the filter `codiscrete ℂ`),
   `L(s) · mellin h (-s) = sign · ε(s) · Ld(1 - s) · mellin k (s - 1)`.

The theorem `Langlands.Global.RankinSelbergGlobal.realPairMellinFactor` proves it.

**Relation to the equation packages.** In the Library's `RealJacquet.UnequalEquation` and
`RealJacquet.EqualEquation` (module `RealJacquetConventionReduction`):
- the `L`-function is `s ↦ ((realPairLFactor ds es).denominator s)⁻¹`;
- the dual `L`-function is `s ↦ ((realPairLFactor dds ees).denominator s)⁻¹`;
- `E` is `s ↦ realPairEpsilon ds es b (NNReal.sqrt ‖a‖₊) _ s`.

The statement allows any `c > 0`, in particular `c = NNReal.sqrt ‖a‖₊`, and any nonzero sign.
So conclusions 3 and 4 are exactly the nonvanishing hypothesis and the factor-identity
hypothesis of `MellinPairContinuationStatement` for these `L`, `Ld`, `E` and `sign`.
Conclusion 2 records the Mellin transforms themselves, so that a theta identity can be
stated for exactly this pair.

## Proof

In the namespace `Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin`:

`exists_factor_pair` (generic construction). Let `D, Dd, E : ℂ → ℂ` be entire with
`StripExpType`, nonzero on a half-plane `Re s > σ₀`, and let `sign ≠ 0`. Take
- `m_h(u) = exp(u²) · sign · E(-u) · D(-u)`;
- `m_k(u) = exp((u + 1)²) · Dd(-u)`.

The proof has four steps:
- Both functions are entire and satisfy `StripDecay`, by the closure lemmas and
  `stripDecay_exp_sq_mul`. For `m_k`, write it as a real shift of `v ↦ exp(v²) Dd(1 - v)`.
- `exists_mellin_eq` gives measurable rapidly decreasing `h, k` with `mellin h = m_h` and
  `mellin k = m_k`. Hence:
  - `mellin h (-s) = sign E(s) exp(s²) D(s)`;
  - `mellin k (s - 1) = exp(s²) Dd(1 - s)`;
  - `mellin k (-s) = exp((1 - s)²) Dd(s)`.

  The first two formulas are part of the conclusion. The third is the second with `s`
  replaced by `1 - s`.

  For `Re s > σ₀`, `mellin h (-s)` and `mellin k (-s)` are nonzero, because `D(s)`, `E(s)`
  and `Dd(s)` are nonzero there. The reflected transform `mellin k (s - 1)` does not have
  this property. It is nonzero exactly where `Dd(1 - s)` is nonzero. By the hypothesis this
  holds for `Re s < 1 - σ₀`, but `mellin k (s - 1)` may vanish elsewhere. The factor
  comparison below excludes its zeros, which form a discrete set.
- The zero sets of `D` and of `s ↦ Dd(1 - s)` are discrete, because these functions are
  analytic and not identically zero (`AnalyticOnNhd.preimage_zero_mem_codiscrete`).
- Off these zeros, both sides of the factor identity equal `sign E(s) exp(s²)`.

In the namespace `Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairFactor`:
- `block_lFactor_stripExpType`: each block denominator has exponential type. For a character
  block, `(RealBlock.character d).lFactor` is `gammaReal.shift e`, with denominator
  `s ↦ Γ_ℝ(s + e)⁻¹`. For an induced block it is `gammaComplex.shift e`, with denominator
  `s ↦ Γ_ℂ(s + e)⁻¹`.
- `realLFactor_stripExpType`: the denominator of `realLFactor xs` is the product of the block
  denominators (`denominator_realLFactor`), so it has exponential type (`list_prod`).
- `block_lFactor_ne_zero`, `realLFactor_ne_zero`: these denominators are nonzero on a right
  half-plane. They are nonzero when `Re(s + e) > 0` for every block shift `e`, since `Γ_ℝ` and
  `Γ_ℂ` do not vanish on `Re > 0`.
- `block_epsilon_stripExpType`, `block_epsilon_differentiable`: by the Library's formulas
  `RealCharacterData.coe_epsilon` and `ComplexCharacterData.coe_realInducedEpsilon`, each block
  ε-factor is a constant times `|b|^(s-1)` or `|b|^(2(s-1))`. It is therefore entire and of
  exponential type.
- `realEpsilon_stripExpType`, `realEpsilon_differentiable`: the same for the product
  `realEpsilon xs b c hc`, by induction on the list. It is nonzero since it is a unit.
- `realPairMellinFactor`: applies `exists_factor_pair` to `D = (realPairLFactor ds es).denominator`,
  `Dd = (realPairLFactor dds ees).denominator`, `E = realPairEpsilon ds es b c hc` and
  `σ₀ = max σa σb`. Here `σa` and `σb` come from `realLFactor_ne_zero` for the two pair block
  lists.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §4.2, pp. 22–23, defines a `(σ, ψ)`
pair. It is a pair of functions `h, k ∈ S(F^×)` depending only on `|t|_F` such that
- `∫ h(t) |t|^(-s) d^×t = ε(s, σ, ψ) e^(P(s)) / L(s, σ)`;
- `∫ k(t) |t|^(-s) d^×t = e^(P(1-s)) / L(s, σ̃)`,

for a quadratic polynomial `P(s) = A s² + B s + C` with `A > 0`. Jacquet justifies existence by
the inverse Mellin transform (§4.1, p. 22) and by bounds in vertical strips (pp. 22–23).

**Relation to the Lean construction.** With `D = L⁻¹` and `Dd = Ld⁻¹` the denominators, the
construction above gives, wherever these denominators do not vanish:
- `mellin h (-s) = sign ε(s) e^(s²) / L(s)`;
- `mellin k (-s) = e^((1-s)²) / Ld(s)`.

So when `dds, ees` present the contragredients, `(h, k)` has the shape of Jacquet's pair:
- `P(s) = s²`;
- `ε(s, σ, ψ)` is replaced by `sign` times the Library's `realPairEpsilon`;
- `L(s, σ)` and `L(s, σ̃)` are the Library's pair factors;
- Jacquet's integral over `F^×` of a radial function is replaced by Mathlib's Mellin transform
  on `(0, ∞)` (they differ by a positive constant depending on `F` and the measure).

**Not proved here.**
- Smoothness of `h` and `k` and membership in `S(F^×)`. Only measurability and rapid decay
  are proved, which is what `MellinPairContinuationStatement` uses.
- That the block lists `dds, ees` present the contragredient representations, and that
  `realPairEpsilon` is Jacquet's `ε(s, σ, ψ)`. The statement holds for arbitrary block lists
  and does not need these identifications.
- The theta identity (Jacquet (4.1)) for real Rankin–Selberg integrals against this pair. It
  is the remaining hypothesis of `MellinPairContinuationStatement`. The module
  `ArchimedeanRealPairIdentity` derives it from Jacquet's pair identity, which stays a
  hypothesis there.
