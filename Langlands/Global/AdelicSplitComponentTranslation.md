# Translation by a centralizing adelic point on the fundamental domain of `P₀(F)`

Module `Langlands.Global.AdelicSplitComponentTranslation`. Main result:
`Langlands.Global.StandardConstantTerm.setLIntegral_mul_left_eq`. Its statement form is
`Langlands.Global.SplitComponentTranslationStatement`, proved by
`Langlands.Global.splitComponentTranslation`.

## Statement

Let `G` be connected reductive over a number field `F`, in an arbitrary universe `u`. Let `i` be a
maximal split torus, `ν` a generic cocharacter and `J ⊆ Δ₀`. Write `P_J`, `L_J`, `U_J` for the
Library's standard parabolic, Levi and unipotent subgroup functors, `Λ₀` for the image of `P₀(F)`
in `G(𝔸)` (`minimalParabolicImage`), and `D₀` for its Library Borel fundamental domain.

Let `a ∈ G(𝔸)` commute with every point of `L_J(𝔸)` and normalize `U_J(𝔸)` (`a w a⁻¹` and
`a⁻¹ w a` lie in `U_J(𝔸)` for `w ∈ U_J(𝔸)`). Let `conjPoints a` be conjugation by `a` on `U_J(𝔸)`,
a continuous group automorphism. Then for every measurable `φ : G(𝔸) → [0, ∞]` left-invariant
under `Λ₀` and under `U_J(𝔸)`:

`∫_{D₀} φ(a g) dg = mulEquivHaarChar (conjPoints a) · ∫_{D₀} φ(g) dg`

with Haar measure on `G(𝔸)`. Here `mulEquivHaarChar` is Mathlib's positive factor by which a
continuous automorphism scales Haar measure: `μ(φ(A)) = mulEquivHaarChar φ · μ(A)`, from
`mulEquivHaarChar_smul_eq_comap`.

The hypotheses on `a` hold for points of the split component of `P_J`. The Library's
`AdelicConstantTermSplitComponent` treats the related commutator property. This module keeps
them as explicit hypotheses.

## Proof

- **Levi factorization** (namespace `Langlands.GroupScheme.StandardLeviFactorization`). On every test
  scheme, every point of `P_J` is a point of `L_J` times a point of `U_J`
  (`exists_levi_mul_unipotent`), and `L_J ∩ U_J` is trivial
  (`eq_one_of_mem_levi_of_mem_unipotent`). Both come from a standard cocharacter `ζ` with
  `P_J = P(ζ)`, `L_J = Z(ζ)`, `U_J = U(ζ)` (`standardCocharacter`) and the Library's dynamic limit
  map: `g (lim g)⁻¹ ∈ U(ζ)`, `lim g ∈ Z(ζ)`, and limits are unique.
- **The factorization of `Λ₀`.** `leviPart J = Λ₀ ∩ L_J(𝔸)`. `leviUnipotentEquiv` is the bijection
  `leviPart J × U_J(F) ≃ Λ₀`, `(x, c) ↦ x c`. Surjectivity factors a rational point of
  `P₀ ⊆ P_J` over `F` and maps the factors to `G(𝔸)` (`exists_leviPart_mul`). Injectivity uses
  `L_J(𝔸) ∩ U_J(𝔸) = 1` (`leviPart_mul_injective`).
- **Conjugation.** `conjPoints a` is a continuous automorphism of `U_J(𝔸)`. By
  `mulEquivHaarChar_smul_eq_comap`, Haar measure satisfies
  `haar(α(C)) = mulEquivHaarChar α · haar(C)`. The inverse of `α` is quasi-measure-preserving,
  because its pushforward of Haar measure is a positive multiple of Haar measure.
- **Assembly.** `LatticeComparison.mul_setLIntegral_mul_left_eq` (module
  `Langlands.Analysis.FundamentalDomainConjugateTranslation`) is applied with `H = G(𝔸)`,
  `V = U_J(𝔸)`, `Λ = Λ₀`, `Γ = U_J(F)`, `M = leviPart J`, and the `Λ₀`-conjugations of
  `ConstantTermAverage` (as in `AdelicStandardConstantTermOperator`). It gives
  `haar(C) ∫_{D₀} φ(a ·) = haar(α(C)) ∫_{D₀} φ`, where `C` is the fundamental domain of `U_J(F)`.
  Cancelling `haar(C)`, which is finite and positive, gives the result.

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §§7.3–7.5 (pp. 214–217). The
translations `σ_α` by split-component points act on weighted spaces of functions on
`P₀(F)U_P(𝔸)\G(𝔸)`, and the source does not spell out the change of measure. This derived module
computes it on the fundamental domain of `P₀(F)`: the factor is the Haar modulus of conjugation by
`a` on `U_J(𝔸)`. It does not identify this factor with the Library's `halfModulus`, and does not
verify the hypotheses on `a` for split-component points.
