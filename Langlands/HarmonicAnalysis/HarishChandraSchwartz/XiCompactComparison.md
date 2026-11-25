# Comparison of `Ξ` for two compact open subgroups, and independence of the Schwartz space

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactComparison`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published modules
`SphericalTranslation` and `RationalWeights` of `Langlands.HarmonicAnalysis.HarishChandraSchwartz`.
Through them it uses `xi`, `iwasawaWeight`, `normalizedHaar`, `IsIwasawaPair` from
[Spherical](Spherical.md); `UniformTranslationBound` and `xi_uniformTranslationBound` (Lemma II.1.2
with `d = 0`) from [SphericalTranslation](SphericalTranslation.md); `weight`, `nu`,
`levelSubmodule`, `schwartzSubmodule` from [Basic](Basic.md); and `rationalXi`,
`rationalMinimalModulus`, `rationalHeight` from [RationalWeights](RationalWeights.md).

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234.

- II.1, printed pp. 250–251 (PDF pp. 16–17): `Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk` for the one
  compact open subgroup `K` fixed in I.1 with `G = P₀ K`.
- Lemma II.1.2, printed p. 251: translation bounds for `Ξ` (used here in the Library's form with
  `d = 0`, `xi_uniformTranslationBound`).
- III.6, printed p. 271 (PDF p. 37): the seminorms `ν_r(f) = sup_g |f(g)| Ξ(g)⁻¹ (1 + σ(g))^r`,
  the spaces `C_H` and `C(G) = ⋃_H C_H`.

**Provenance: derived.** Waldspurger works with one fixed `K` throughout and does not state how
`Ξ` or `C(G)` depends on `K`. The comparison `Ξ_K ≤ C Ξ_{K'}` and the resulting equality of
Schwartz spaces are proved here from the definitions of II.1 and III.6 and Lemma II.1.2; they are
not results of the source. They are needed in the Library because the statements built on
`rationalXi` take an arbitrary compact open `K` with `G(F) = P₀(F) K` as data, while some inputs
(for example Proposition II.4.5 in `RationalConstantTerm`) require further properties of `K`,
such as the Levi Iwasawa decomposition `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`, which a given `K`
need not have. The comparison transfers estimates and Schwartz membership between two such
subgroups.

## Definitions

For a type `G` and functions `Ξ, Ξ' : G → ℝ` (derived notions; Waldspurger writes such
comparisons out with explicit constants):

- **`WeightDominated Ξ Ξ' : Prop`**: there is `C : ℝ` with `Ξ(g) ≤ C Ξ'(g)` for all `g ∈ G`.
  `C` is not required to be positive; for `Ξ > 0` and `Ξ' > 0` (as for `xi`) any such `C` is
  positive.
- **`WeightEquivalent Ξ Ξ' : Prop`** (the recorded declaration): `WeightDominated Ξ Ξ'` and
  `WeightDominated Ξ' Ξ`, i.e. `Ξ` and `Ξ'` agree up to bounded factors in both directions.
  `WeightEquivalent.symm` swaps the two functions.

## Results

### Uniform left translations

For a topological group `G`:

- `UniformTranslationBound.exists_uniform_left`: if `Ξ : G → ℝ` is nonnegative, satisfies
  `UniformTranslationBound Ξ`, and is left invariant under an open subgroup `H`
  (`Ξ(k g) = Ξ(g)` for `k ∈ H`), then for every compact set `C ⊆ G` there is `c : ℝ` with
  `Ξ(x g) ≤ c Ξ(g)` for all `x ∈ C` and all `g ∈ G`.

  *Proof.* For each `l ∈ G` choose `c_l` with `Ξ(l g · 1) ≤ c_l Ξ(g)`. The open sets
  `{x | x l⁻¹ ∈ H}` (`l ∈ G`) cover `C`; take a finite subcover indexed by `t`. For `x ∈ C` pick
  `l ∈ t` with `x l⁻¹ ∈ H`; then `Ξ(x g) = Ξ((x l⁻¹)(l g)) = Ξ(l g) ≤ c_l Ξ(g)`, and
  `c = Σ_{l ∈ t} |c_l|` works.

### Comparison of the weights and of `Ξ`

For a topological group `G`, subgroups `P`, `K`, `K'` with `G = P K` (`hPK`) and `G = P K'`
(`hPK'`), and a character `δ : P →* ℝ≥0ˣ` trivial on `P ∩ K` (`hδ`) and on `P ∩ K'` (`hδ'`):

- `exists_iwasawaWeight_le_mul`: if `K` is open and `K'` is compact, there is `c ≥ 0` with
  `φ_K(g) ≤ c φ_{K'}(g)` for all `g`, where `φ_K = iwasawaWeight hPK δ` is
  `φ_K(p k) = δ(p)^{1/2}`.

  *Proof.* `φ_K` is continuous (`continuous_iwasawaWeight`, using `K` open), so it is bounded by
  some `c` on the compact set `K'`; `c ≥ φ_K(1) ≥ 0`. Write `g = q κ'` with `q ∈ P`, `κ' ∈ K'`.
  Then `φ_K(g) = δ(q)^{1/2} φ_K(κ')` (`iwasawaWeight_mul_left`) and `φ_{K'}(g) = δ(q)^{1/2}`
  (`iwasawaWeight_mul`, using `hδ'`), so `φ_K(g) ≤ c φ_{K'}(g)`.

- `exists_xi_le_mul`: assume further `G` second countable with Borel σ-algebra, `K` and `K'`
  compact (as `CompactSpace` instances) and open. Then there is `C : ℝ` with
  `Ξ_K(g) ≤ C Ξ_{K'}(g)` for all `g ∈ G`, where `Ξ_K = xi hPK δ` and `Ξ_{K'} = xi hPK' δ` are the
  integrals `Ξ_K(g) = ∫_K φ_K(k g) dk` for the normalized Haar measures.

  *Proof.* Let `c` be as in the previous result and, by `exists_uniform_left` applied to
  `Ξ_{K'}` (positive by `xi_pos`, left `K'`-invariant by `xi_mul_left`, with
  `xi_uniformTranslationBound`) and the compact set `K`, let `C₂` satisfy
  `Ξ_{K'}(k g) ≤ C₂ Ξ_{K'}(g)` for all `k ∈ K`. Put `c₀ = ∫_{K'} φ_K(k') dk' > 0` (the integrand
  is continuous and everywhere positive and the measure is a probability measure). Fix `g` and
  consider the continuous function `F(k, k') = φ_K(k' k g)` on `K × K'`.
  - For fixed `k' ∈ K'`, write `k' = q κ` with `q ∈ P`, `κ ∈ K`. Then
    `F(k, k') = δ(q)^{1/2} φ_K(κ k g)`, and left invariance of the Haar measure of `K` gives
    `∫_K F(k, k') dk = δ(q)^{1/2} Ξ_K(g) = φ_K(k') Ξ_K(g)`. Integrating over `K'`:
    `∫_{K'} ∫_K F = c₀ Ξ_K(g)`.
  - For fixed `k ∈ K`, `F(k, k') ≤ c φ_{K'}(k' k g)`, so
    `∫_{K'} F(k, k') dk' ≤ c Ξ_{K'}(k g) ≤ c C₂ Ξ_{K'}(g)`.
  - By Fubini (`integral_integral_swap`), `c₀ Ξ_K(g) = ∫_K ∫_{K'} F ≤ c C₂ Ξ_{K'}(g)`.

  Hence `C = c C₂ / c₀` works.

- `xi_weightEquivalent`: under the same hypotheses,
  `WeightEquivalent (xi hPK δ) (xi hPK' δ)`, by `exists_xi_le_mul` applied in both directions.

### Seminorms, level spaces and Schwartz spaces

For a type `G` and functions `Ξ, Ξ', σ : G → ℝ` with `Ξ > 0`, `Ξ' > 0`, `σ ≥ 0` everywhere and
`Ξ(g) ≤ C Ξ'(g)` for all `g`:

- `weight_le_ofReal_mul_weight`: `Ξ'(g)⁻¹ (1 + σ(g))^r ≤ C Ξ(g)⁻¹ (1 + σ(g))^r` as extended
  nonnegative reals (`weight Ξ' σ r g ≤ ofReal C * weight Ξ σ r g`) for all real `r` and `g`.
  (`C ≥ 0` follows from the hypotheses.)
- `nu_le_ofReal_mul_nu`: `ν'_r(f) ≤ C ν_r(f)` for every `f : G → ℂ` and every real `r`, where `ν`
  and `ν'` are the seminorms `nu` built from `Ξ` and from `Ξ'` with the same `σ`.
- `levelSubmodule_le_of_le_mul` (`G` a group): for every subgroup `H`,
  `levelSubmodule Ξ σ H ≤ levelSubmodule Ξ' σ H` (bi-`H`-invariance is unchanged; finiteness of
  every `ν_r` passes through the previous bound).
- `schwartzSubmodule_le_of_le_mul` (`G` a topological group):
  `schwartzSubmodule Ξ σ ≤ schwartzSubmodule Ξ' σ`, by monotonicity of the union over compact
  open subgroups.
- `schwartzSubmodule_eq_of_le_mul`: if also `Ξ'(g) ≤ C' Ξ(g)` for all `g`, then
  `schwartzSubmodule Ξ σ = schwartzSubmodule Ξ' σ`.
- `schwartzSubmodule_eq_of_weightEquivalent`: the same conclusion from
  `WeightEquivalent Ξ Ξ'` (with `Ξ, Ξ' > 0`, `σ ≥ 0`).

### Actual rational points

Setting of [RationalWeights](RationalWeights.md): `F` a nonarchimedean local field, `G` a group
scheme over `Spec F` (affine morphism, locally of finite type), `G(F) = rationalPoints G` with its
canonical topology and Borel σ-algebra, `i : S → G` and `ν` defining
`P₀(F) = standardParabolicPoints i ν ∅`, and `δ₀ = rationalMinimalModulus i ν`. `K` and `K'` are
subgroups of `G(F)` that are open (`hKo`, `hK'o`) and compact (`hKc`, `hK'c`), with
`G(F) = P₀(F) K` (`hPK`) and `G(F) = P₀(F) K'` (`hPK'`).

- `exists_rationalXi_le_mul`: there is `C : ℝ` with
  `rationalXi hKc hPK g ≤ C · rationalXi hK'c hPK' g` for all `g ∈ G(F)`. This is
  `exists_xi_le_mul` with `δ = δ₀`, whose triviality on `P₀(F) ∩ K` and `P₀(F) ∩ K'` is
  `rationalMinimalModulus_eq_one`; second countability of `G(F)` is
  `rationalPoint_secondCountableTopology`.
- `rationalXi_weightEquivalent`:
  `WeightEquivalent (rationalXi hKc hPK) (rationalXi hK'c hPK')`, from `exists_rationalXi_le_mul`
  in both directions.
- `rationalSchwartzSubmodule_eq`: for every matrix representation `ρ : MatrixRepresentation G n`
  (`n` a nonempty finite type), with `σ = rationalHeight ρ`,
  `schwartzSubmodule (rationalXi hKc hPK) σ = schwartzSubmodule (rationalXi hK'c hPK') σ`.
  Proof: `exists_rationalXi_le_mul` in both directions, `rationalXi_pos`, `rationalHeight_nonneg`
  and `schwartzSubmodule_eq_of_le_mul`.

## Scope

- No condition on `K` or `K'` beyond compact, open and `G = P K = P K'` (and, generically, `δ`
  trivial on `P ∩ K`, `P ∩ K'`) is used; in particular neither subgroup need be special or
  maximal.
- The constants are not explicit, and only `Ξ` is compared; the height `σ` is the same on both
  sides.
- The module does not compare Schwartz spaces for different heights `σ`, nor topologies on
  `C(G)`; it compares only the underlying subspaces of `G → ℂ`.

The module also re-exports [the modular-character comparison](XiCompactModularComparison.md), whose separate statement retains its locally compact and unimodular hypotheses.
