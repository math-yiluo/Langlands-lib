# Translation bounds for `Ξ` (Waldspurger, Lemma II.1.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalTranslation`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published modules
`Convolution`, `SphericalInverse`, `SquareIntegrability` and `Translations` of
`Langlands.HarmonicAnalysis.HarishChandraSchwartz`. Through them it uses `xi`,
`normalizedHaar`, `IsIwasawaPair` and Lemma II.1.3 (`integral_xi_mul_mul`) from
[Spherical](Spherical.md), Lemma II.1.4 (`xi_inv`, `modular_eq_one_of_mem`) from
[SphericalInverse](SphericalInverse.md), `TranslationBound`, `HeightTranslationBound`
and `TranslationWeights` from [Translations](Translations.md), `ConvolutionWeights`
from [Convolution](Convolution.md) and `SquareIntegrableWeight` from
[SquareIntegrability](SquareIntegrability.md).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.

- Lemma II.1.2, printed p. 251 (PDF p. 17): there is `d ∈ ℕ` such that for all
  `g₁, g₂ ∈ G` there is `C > 0` with

  `Ξ(g₁ g g₂) ≤ C Ξ(g) (1 + σ(g))^d` for all `g ∈ G`.

- Lemma II.1.3, printed p. 252 (PDF p. 18): `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)` for all
  `g₁, g₂ ∈ G`.
- Section III.6, printed pp. 271–272 (PDF pp. 37–38): the translations
  `ρ(g₁)λ(g₂)` preserve `C(G)` "cf. I.6 et Lemme II.1.2", and Lemma III.6.1 on
  convolution, whose proof uses Lemmas II.1.3–II.1.5. The generic forms of these
  results are in `Translations` and `Convolution`; their hypotheses on the weights are
  `TranslationWeights` and `ConvolutionWeights`.

## Scope

`Ξ` is the function `xi hPK δ` of Spherical, defined by the integral formula
`Ξ(g) = ∫_K δ(p(kg))^{1/2} dk` from generic data: a topological group `G` with Borel
measurable structure, subgroups `P` and `K` with `K` compact and `G = P K`
(`hPK : IsIwasawaPair P K`), and a character `δ : P →* ℝ≥0ˣ` playing the role of
`δ₀ ∘ m₀`. As stated in Spherical, the identification of this integral with the
matrix coefficient `⟨π(g)e, e⟩` of `I_{P₀}^G 1`, and the specialization to a reductive
`p`-adic group, its `P₀`, `K` and `δ₀`, are not done here.

The module proves Lemma II.1.2 for `xi` in a stronger form than Waldspurger's: the
exponent `d` can be taken to be `0`, so the bound `Ξ(g₁ g g₂) ≤ C Ξ(g)` holds without a
polynomial factor in `σ`, and therefore for every function `σ`. The proof is not
Waldspurger's; see the proof notes.

## Definitions

- `UniformTranslationBound Ξ : Prop` for `Ξ : G → ℝ` on a group `G`: for all
  `g₁, g₂ ∈ G` there is `C : ℝ` with `Ξ(g₁ g g₂) ≤ C Ξ(g)` for all `g ∈ G`. This is the
  conclusion of Lemma II.1.2 with `d = 0`. As in `TranslationBound`, `C` is not
  required to be positive; for positive `Ξ` the inequality at `g = 1` forces `C > 0`.

## Results

Generic consequences, for any group `G` and any `Ξ : G → ℝ`:

- `UniformTranslationBound.translationBound`: `UniformTranslationBound Ξ` implies
  `TranslationBound Ξ σ` (Lemma II.1.2 in the form of `Translations`) with `d = 0`, for
  every `σ : G → ℝ`.
- `UniformTranslationBound.exists_le_mul`: the reverse comparison; for all `g₁, g₂`
  there is `C` with `Ξ(g) ≤ C Ξ(g₁ g g₂)` for all `g`.

For the next two results `G` is a topological group and `K` is an open subgroup;
`measureReal_setOf_mul_mul_mem_pos` also assumes `G` Borel and `K` compact.

- `isOpen_setOf_mul_mul_mem`: for `a, b ∈ G`, the set `{k ∈ K | a k b ∈ K}` is open in
  `K`.
- `measureReal_setOf_mul_mul_mem_pos`: if `a b ∈ K`, this set has positive measure for
  `normalizedHaar K`. With `b = a⁻¹` the set is `K ∩ a⁻¹ K a`.

The following results assume, as Lemma II.1.3 in Spherical does: `G` a topological
group, second countable, with Borel measurable structure; `K` compact and open;
`G = P K`; and `δ` trivial on `P ∩ K` (`hδ`).

- `measureReal_mul_xi_le`: if `S ⊆ K` is measurable and `Ξ(g₁ k g₂) = Ξ(g₁ g₂)` for
  all `k ∈ S`, then `mes(S) Ξ(g₁ g₂) ≤ Ξ(g₁) Ξ(g₂)`, where `mes = normalizedHaar K`.
- `xi_mul_le_left`: `Ξ(g₁ g) ≤ Ξ(g₁) / mes(K ∩ g₁⁻¹ K g₁) · Ξ(g)` for all `g₁, g`,
  with `K ∩ g₁⁻¹ K g₁` written as `{k ∈ K | g₁ k g₁⁻¹ ∈ K}`.
- `xi_mul_le_right`: `Ξ(g g₂) ≤ Ξ(g₂) / mes(K ∩ g₂ K g₂⁻¹) · Ξ(g)` for all `g, g₂`,
  with `K ∩ g₂ K g₂⁻¹` written as `{k ∈ K | g₂⁻¹ k g₂ ∈ K}`.
- `xi_uniformTranslationBound` (**Lemma II.1.2 with `d = 0`**):
  `UniformTranslationBound (xi hPK δ)`, with
  `C = Ξ(g₁) / mes(K ∩ g₁⁻¹ K g₁) · Ξ(g₂) / mes(K ∩ g₂ K g₂⁻¹)`.
- `xi_translationBound`: `TranslationBound (xi hPK δ) σ` for every `σ`.
- `xi_translationWeights`: `TranslationWeights (xi hPK δ) σ` for every `σ ≥ 0` with
  `HeightTranslationBound σ`. The translation results of `Translations` (that
  `ρ(g₁)λ(g₂)` maps `C(G)` continuously to itself) therefore apply to `Ξ = xi`. For a
  nonnegative subadditive `σ`, such as the height of `Height`,
  `heightTranslationBound_of_le_add` (in `Translations`) gives
  `HeightTranslationBound σ`.

Assembly of the hypotheses of the generic Lemma III.6.1:

- `xi_convolutionWeights`: `ConvolutionWeights μ K (xi hPK δ) σ` holds under the
  following hypotheses: `G` a locally compact, second countable topological group with
  Borel measurable structure, unimodular (`modularCharacter g = 1` for all `g`); `P`
  closed and locally compact; `K` compact and open; `δ` equal to the modular character
  of `P` (`hδ : δ p = modularCharacter p`); `σ` nonnegative, continuous, subadditive
  (`σ(g h) ≤ σ(g) + σ(h)`) and left `K`-invariant; and `SquareIntegrableWeight μ
  (xi hPK δ) σ`, the statement of Lemma II.1.5 for the measure `μ`. The fields come
  from `xi_pos`, `continuous_xi`, `xi_mul_left` and `integral_xi_mul_mul` (Spherical),
  `xi_inv` (Lemma II.1.4, SphericalInverse), `one_add_le_of_le_add` (Convolution) and
  the hypotheses on `σ`; triviality of `δ` on `P ∩ K` follows from
  `modular_eq_one_of_mem`.

Lemma II.1.5 for `xi` is not proved here: `SquareIntegrability` derives
`SquareIntegrableWeight` from the hypothesis structure `CartanSquareBound`, which
records Cartan decomposition data, the upper bounds of I.1 (5) and of Lemma II.1.1,
and the lower bound of I.1 (6). These are not established for `xi`. It remains a hypothesis of `xi_convolutionWeights`.
`ConvolutionWeights` does not mention `TranslationBound`; II.1.2 is used by the
translation results, not by Lemma III.6.1.

## Proof notes

Waldspurger proves Lemma II.1.2 with the matrix-coefficient description
`Ξ(g₁ k₁ g k₂ g₂) = ⟨π(g)v₂, v₁⟩`, the asymptotics of Proposition I.4.3 on the
positive chamber, the lower bound of Lemma II.1.1 and the Cartan decomposition I.1 (4).
This gives the polynomial factor `(1 + σ(g))^d`.

The Lean proof uses only Lemma II.1.3 and the bi-`K`-invariance of `Ξ`:

1. `measureReal_mul_xi_le`: if `Ξ(g₁ k g₂) = Ξ(g₁ g₂)` for `k ∈ S`, then
   `mes(S) Ξ(g₁ g₂) = ∫_S Ξ(g₁ k g₂) dk ≤ ∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`. The
   inequality uses `Ξ > 0`; the integrand is continuous on the compact group `K`, hence
   integrable; the last equality is Lemma II.1.3.
2. Left translations. For `k ∈ S = K ∩ g₁⁻¹ K g₁` one has
   `g₁ k g = (g₁ k g₁⁻¹)(g₁ g)` with `g₁ k g₁⁻¹ ∈ K`, so `Ξ(g₁ k g) = Ξ(g₁ g)` by left
   `K`-invariance. `S` is open in `K` and contains `1`, so `mes(S) > 0`
   (`measureReal_setOf_mul_mul_mem_pos`, using that a Haar measure charges nonempty
   open sets). Step 1 gives `Ξ(g₁ g) ≤ Ξ(g₁)/mes(S) · Ξ(g)`.
3. Right translations. For `k ∈ K ∩ g₂ K g₂⁻¹` one has
   `g k g₂ = (g g₂)(g₂⁻¹ k g₂)` with `g₂⁻¹ k g₂ ∈ K`, and right `K`-invariance gives
   `Ξ(g k g₂) = Ξ(g g₂)`; step 1 then bounds `Ξ(g g₂)` by a constant times `Ξ(g)`.
4. `Ξ(g₁ g g₂) = Ξ(g₁ (g g₂))`: apply step 2, then step 3 (the constant of step 2 is
   nonnegative).
