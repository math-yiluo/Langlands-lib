# Pair factors of archimedean Weil-group presentations

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.LocalFactor.Archimedean`. The module defines the pair `L`- and `ε`-factors of two
presentations by archimedean Weil-group blocks. A presentation is a list of the Library's
blocks: `RealBlock` for `W_ℝ`, `ComplexCharacterData` for `W_ℂ`. The pair factor of `ds` and
`ds'` is the published factor of a block list for the tensor product `σ ⊗ σ'` of the
represented Weil-group representations. These are the archimedean pair factors
`L(s, φ_v ⊗ φ'_v)` and `ε(s, φ_v ⊗ φ'_v, ψ_v)` of the Rankin–Selberg functional equation, on
the Weil-group side.

## Declarations

### Operations on characters

- `complexConjugation : W_ℂ →ₜ* W_ℂ` is `z ↦ z̄`, with `coe_complexConjugation`.
- `RealCharacterData.mul c d` is the product character `c d` of `ℝˣ`. Its parity is
  `c.parity + d.parity` in `Fin 2`, and its exponent is the sum of the exponents. The
  defining equation `χ(x) = sgn(x)^e |x|^t` is proved from those of `c` and `d`, using
  `sgn(x)² = 1` and `|x|^{t₁}|x|^{t₂} = |x|^{t₁+t₂}`.
- `ComplexCharacterData.mul c d` is the product character `c d` of `ℂˣ`, with added weights
  and exponents. The equation `χ(z) = (z/|z|)^m |z|^{2t}` is proved.
- `ComplexCharacterData.conj d` is `z ↦ d(z̄)`, with weight `-m` and the same exponent. Its
  equation uses `z̄/|z| = (z/|z|)⁻¹`.
- `ComplexCharacterData.twistReal d c` is `z ↦ d(z) · c(z z̄)`, the twist of a character of
  `ℂˣ` by a character of `ℝˣ` composed with the norm `N(z) = z z̄ = |z|²`
  (`complexNorm`). It has the same weight and exponent `t + t'`. The equation uses
  `sgn(|z|²) = 1` and `(|z|²)^{t'} = |z|^{2t'}`.

### Tensor products of blocks

`RealBlock.tensor x y : List RealBlock` is defined case by case:

| `x` | `y` | `x.tensor y` |
| --- | --- | --- |
| character `c` | character `d` | `[character (c.mul d)]` |
| character `c` | induced `d` | `[induced (d.twistReal c)]` |
| induced `d` | character `c` | `[induced (d.twistReal c)]` |
| induced `d` | induced `e` | `[induced (d.mul e), induced (d.mul e.conj)]` |

`RealBlock.realRank_tensor` proves that the rank of `x.tensor y` is `rank x · rank y`.

- `realPairBlocks xs ys` concatenates `x.tensor y` over all pairs, with `xs` in the outer
  loop. `realRank_realPairBlocks` proves that its rank is `realRank xs · realRank ys`. The
  auxiliary lemmas are `realRank_append` and `realRank_flatMap_tensor`.
- `complexPairBlocks xs ys` is the list of all products `x.mul y`.
  `length_complexPairBlocks` proves that its length is the product of the lengths.

### Pair factors

- `realPairLFactor xs ys = realLFactor (realPairBlocks xs ys)`,
  `realPairStandardEpsilon xs ys = realStandardEpsilon (realPairBlocks xs ys)` and
  `realPairEpsilon xs ys a c hc s = realEpsilon (realPairBlocks xs ys) a c hc s`. They use the
  published presentation factors of `ArchimedeanPresentation`: products of the block
  factors `Γ_ℝ` and `Γ_ℂ`, and of the standard and twisted `ε`-factors with their additive
  character and measure conventions.
- `complexPairLFactor`, `complexPairStandardEpsilon` and `complexPairEpsilon` are the same
  over `ℂ`, with `complexLFactor`, `complexStandardEpsilon` and `complexEpsilon`.

### Independence of the order of the blocks

- `realPairBlocks_perm` and `complexPairBlocks_perm`: permuting either presentation permutes
  the block list of the pair presentation. The proof uses Mathlib's `List.Perm.flatMap_left`
  and `List.Perm.flatMap_right`.
- `realPairLFactor_perm`, `realPairEpsilon_perm`, `complexPairLFactor_perm` and
  `complexPairEpsilon_perm`: the pair factors of presentations that agree up to the order of
  their blocks are equal. They follow from the published `realLFactor_perm`,
  `realEpsilon_perm`, `complexLFactor_perm` and `complexEpsilon_perm`. So parameters attached
  only up to permutation of blocks have well-defined pair factors.

### Additive characters and measures

The `ε`-factors are those of the published `ArchimedeanScaling` and `ArchimedeanPresentation`.
For the real field, `realPairEpsilon xs ys a c hc s` uses the additive character
`x ↦ e^{2πi a x}` (`realScaledCharacter a`, built from `Real.fourierChar`) and the measure
`c · dx` (`realScaledMeasure c hc`, a multiple of Lebesgue measure). For the complex field,
`complexPairEpsilon xs ys a c hc s` uses `z ↦ e^{2πi Tr(a z)}` (`complexScaledCharacter a`)
and the measure `c · 2 dx dy` (`complexScaledMeasure c hc`, a multiple of twice Euclidean
area). At `a = 1` and `c = 1` these are Tate's standard characters and their self-dual
measures. There the `ε`-factors are the standard ones, `realPairStandardEpsilon` and
`complexPairStandardEpsilon`, by the published `realEpsilon_standard` and
`complexEpsilon_standard`. The variable `s` is the twist by `|·|^s`.

## Source correspondence

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
  literature ID `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`. The PDF page is the
  printed page plus nine.
  - (2.2.2), printed p.10 (PDF p.19): representations of `W_ℝ` are sums of characters and of
    representations `Ind_{W_ℂ}^{W_ℝ} μ`.
  - §3.1–3.3, printed pp.12–14 (PDF pp.21–23): archimedean `L`- and `ε`-factors of characters
    and of induced representations.
  - (3.4.1)–(3.4.2) and (3.4.8), printed pp.14–15 (PDF pp.23–24): `L` and `ε` are additive
    in exact sequences and inductive in degree zero. So the factor of a sum is the product of
    the factors.
- A. W. Knapp, *Local Langlands correspondence: the archimedean case*, Proc. Sympos. Pure
  Math. 55, Part 2 (1994), literature ID `knapp-1994-archimedean-llc`, SHA256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`. Printed pp.401–403
  (PDF pp.411–413), (3.1)–(3.3) and the Lemma on p.403: the irreducible representations of
  `W_ℝ` are characters `(±, t)` and two-dimensional `(ℓ, t)`, and semisimple representations
  are sums of these.

### Derived formulation

1. **Tensor products as block lists.** The table is the standard decomposition of tensor
   products of `W_ℝ`-representations. A character `χ` of `W_ℝ` restricts on `W_ℂ = ℂˣ` to
   `z ↦ χ_ℝ(z z̄)`. In the published `RealCharacterData.representation` the character of
   `ℝˣ` is pulled back along `RealWeil.abelianCoordinate`, which sends `z` to `|z|²`. The
   projection formula `χ ⊗ Ind(μ) ≅ Ind(μ · χ|_{ℂˣ})` gives the middle rows, and
   `Ind(μ) ⊗ Ind(ν) ≅ Ind(μ ⊗ Res Ind(ν)) = Ind(μν) ⊕ Ind(μν̄)` gives the last row. Over `ℂ`,
   characters of `W_ℂ` multiply. These isomorphisms of representations are mathematical
   explanations and are not proved in Lean. The ranks are proved.
2. **Factors.** By additivity, the factors of `σ ⊗ σ'` are the products of the factors of the
   blocks of the decomposition, which are the published presentation factors of
   `realPairBlocks` and `complexPairBlocks`. Weight-zero induced blocks are allowed, as in
   the Library, and are read as sums of two characters (`Γ` duplication). The ordering of the
   blocks does not affect the products.
3. **Additive characters and measures.** `realPairEpsilon` and `complexPairEpsilon` take the
   twisting parameter `a` and measure scale `c` of the published `realEpsilon` and
   `complexEpsilon`, with the normalization stated above. No new normalization is
   introduced.

## Scope

The module does not prove that `realModel (realPairBlocks xs ys)` is isomorphic to the tensor
product of `realModel xs` and `realModel ys`. Beyond reordering of blocks, it does not prove
independence of the pair factors from the chosen presentations: the published
presentation-independence statement covers single presentations. It also does not compare
these factors with archimedean Rankin–Selberg integrals (Jacquet). These are theorem
obligations.
