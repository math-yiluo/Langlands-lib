# Arthur's alternating-sum identity and the expansion of `τ τ̂` in `σ`

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsAlternating`. It
imports only `Langlands.LinearAlgebra.ArthurCombinatoricsStatement` and
changes no published file.

It is part of the proof of
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement`,
assembled in `Langlands.LinearAlgebra.ArthurCombinatoricsProof`. It proves
two of the six conjuncts, each as its own named theorem:

```lean
theorem Langlands.ArthurCombinatorics.alternatingSumStatement :
    AlternatingSumStatement.{u}
theorem Langlands.ArthurCombinatorics.tauTauHatSigmaExpansionStatement :
    TauTauHatSigmaExpansionStatement.{u}
```

The other four conjuncts need the geometric input that every weight
`weightCoordinate P Θ i` is a nonnegative combination of the simple roots
`α_k`, `k ∈ Θ` (module `ArthurCombinatoricsCartanInverse`). They are proved in
other modules: `TauTauHatVanishingStatement` and
`SigmaCharacterizationStatement` in `ArthurCombinatoricsSigma`,
`LanglandsCombinatorialLemmaStatement` in
`ArthurCombinatoricsLanglandsLemma`, and `SigmaSupportStatement` in
`ArthurCombinatoricsSigmaSupport`. `alternatingSum_eq` is also used there.

## Proofs

**`alternatingSum_eq`** (for finite sets of any type, used by both theorems):
for `Θ₁ ⊆ Θ₂`, `∑_{Θ₁ ⊆ Θ ⊆ Θ₂} (−1)^{|Θ₂ \ Θ|}` is `1` if `Θ₁ = Θ₂` and `0`
otherwise. The map `Θ ↦ Θ₂ \ Θ` is a bijection from the interval
`{Θ : Θ₁ ⊆ Θ ⊆ Θ₂}` (written `Θ₂.powerset.filter (Θ₁ ⊆ ·)`) onto the powerset
of `Θ₂ \ Θ₁`, with inverse `T ↦ Θ₂ \ T` (`Finset.sum_nbij'`). Mathlib's
`Finset.sum_powerset_neg_one_pow_card` evaluates the reindexed sum
`∑_{T ⊆ Θ₂ \ Θ₁} (−1)^{|T|}` as `1` if `Θ₂ \ Θ₁ = ∅` and `0` otherwise, and
`Θ₂ \ Θ₁ = ∅` exactly when `Θ₁ = Θ₂`. `alternatingSumStatement` is this lemma
at universe `u`.

**`tauTauHatSigmaExpansionStatement`.** Write `S = b.support`. By definition
`σ_{Θ₁}^{Θ₂}(H) = ∑_{Θ₂ ⊆ Θ₃ ⊆ S} (−1)^{|Θ₃ \ Θ₂|} τ_{Θ₁}^{Θ₃}(H) τ̂_{Θ₃}^S(H)`.
Exchanging the two sums (`Finset.sum_comm'`; the pairs are those with
`Θ_P ⊆ Θ₂ ⊆ Θ₃ ⊆ S`) gives

`∑_{Θ_P ⊆ Θ₃ ⊆ S} (∑_{Θ_P ⊆ Θ₂ ⊆ Θ₃} (−1)^{|Θ₃ \ Θ₂|}) τ_{Θ₁}^{Θ₃}(H) τ̂_{Θ₃}^S(H)`.

By `alternatingSum_eq` the inner sum is `1` if `Θ_P = Θ₃` and `0` otherwise
(`Finset.sum_ite_eq`), so only `Θ₃ = Θ_P` remains, and `Θ_P` lies in the range
of summation because `Θ_P ⊆ S`. The hypothesis `Θ₁ ⊆ Θ_P` and the
root-system structure are not used: the identity is purely combinatorial.

## Provenance

- `AlternatingSumStatement` is Arthur, *A trace formula for reductive groups
  I* (1978), Proposition 1.1, p.916 (registered as
  `arthur-1978-trace-formula-reductive-groups-I`; PDF page = printed page −
  910, so PDF page 6). Arthur proves it in the same way, as the binomial
  expansion of `(1 − 1)^{|Θ₂ \ Θ₁|}`.
- `TauTauHatSigmaExpansionStatement` is Arthur, *An introduction to the trace
  formula* (2005), (8.2), §8, p.41 (in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`; PDF page = printed
  page + 12, so PDF page 53). Arthur derives it from Identity 6.2 (p.31,
  PDF 43) as here: insert the definition of `σ` and apply the alternating sum
  to the inner sum.

These locators lie in the ranges recorded in the
published statement Markdown (`ArthurCombinatoricsStatement.md`), which cite
§8, pp.40–42 for (8.2) and Lemma 8.3. The page numbers above were checked
against the PDF.

## Axioms

The module compiles without warnings. The lake-build
inspection of `tauTauHatSigmaExpansionStatement` (which uses
`alternatingSum_eq`) reports only `propext`, `Classical.choice` and
`Quot.sound`.
