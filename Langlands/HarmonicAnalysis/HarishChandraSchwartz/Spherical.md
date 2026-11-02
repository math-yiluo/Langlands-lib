# The spherical function `Ξ` from a factorization `G = P K`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical`,
namespace `Langlands.HarishChandraSchwartz`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, section II.1 (printed
pp. 250–252, PDF pp. 16–18). Waldspurger takes the trivial representation `1` of
`M₀`, the induced representation `π = I_{P₀}^G 1`, and the unique `K`-invariant
vector `e` with `e(1) = 1`, and defines `Ξ(g) = ⟨π(g)e, e⟩`. He then records the
integral formula

`Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk`.

Here `G = P₀ K` (I.1, printed p. 240, PDF p. 6), `δ₀` is the modulus character of
the minimal parabolic subgroup `P₀ = M₀ U₀`, and `m₀(g)` is the `M₀`-component in a
factorization `g = u₀(g) m₀(g) k₀(g)` with `u₀(g) ∈ U₀`, `k₀(g) ∈ K`. The Haar
measure on `K` has total mass one (I.1, same page: `mes(H ∩ K) = 1`). The function `Ξ` is the first weight in the seminorms `ν_r`
of III.6 (`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic`).

## Scope

This module takes the integral formula as the definition of `Ξ` and constructs it
from abstract data of the same shape:

- `G` is a topological group, with a measurable structure that is Borel;
- `P` and `K` are subgroups, `K` is compact, and `G = P K` (`IsIwasawaPair P K`);
- `δ : P →* ℝ≥0ˣ` is a positive character of `P`, which plays the role of `δ₀ ∘ m₀`.

The results assume that `δ` is trivial on `P ∩ K`. This holds for `δ₀ ∘ m₀`: it is a
continuous positive character, so it is trivial on the compact group `P₀ ∩ K`. For
continuity, integrability of the integrand, positivity and Lemma II.1.3, `K` is
assumed open, as it is for Waldspurger's `K` in the `p`-adic group `G`.

The module does not construct `G`, `P₀`, `K` or `δ₀` for a reductive group. Taking
`P = P₀`, Waldspurger's `K` and `δ = δ₀ ∘ m₀` is a specialization of the generic
data, to be made once the reductive group and these subgroups are available.

The module also does not identify the integral with the matrix coefficient
`⟨π(g)e, e⟩` of the normalized induced representation `π = I_{P₀}^G 1`. That
identification is a representation-theoretic comparison which remains to be proved
on the representation framework; it is an open proof obligation, not an assumption
that a consumer may supply. The bounds of II.1.1, and II.1.2 and II.1.5, use
the Cartan decomposition and the asymptotics of Proposition I.4.3. Waldspurger
derives II.1.4 (`Ξ(g⁻¹) = Ξ(g)`) from `π̌ = π`; from the integral formula it needs
the integration formula for `G = P₀ K` with `δ₀` the modulus character. None of
these is stated or proved here.

## Definitions

- `normalizedHaar H`: for a compact group `H`, the Haar measure `haarMeasure ⊤` of
  total mass one. Instances: it is a Haar measure, a probability measure, and right
  invariant (because the modular character of a compact group is trivial).
- `IsIwasawaPair P K`: every `g ∈ G` can be written as `g = p k` with `p ∈ P` and
  `k ∈ K`. This is the decomposition `G = P₀ K` of Waldspurger I.1.
- `iwasawaFactor hPK g`: a chosen `p ∈ P` with `g ∈ p K`; `exists_iwasawaFactor`
  records that such a `k` exists.
- `iwasawaWeight hPK δ g = δ(p)^{1/2}` for `g = p k`, defined through the chosen
  factor. For `P = P₀` and `δ = δ₀ ∘ m₀` this is the function `g ↦ δ₀(m₀(g))^{1/2}`.
- `xi hPK δ g = ∫_K iwasawaWeight hPK δ (k g) dk`, with respect to
  `normalizedHaar K`. This is Waldspurger's `Ξ`.

## Results

For the weight, assuming `δ` is trivial on `P ∩ K`:

- `iwasawaWeight_mul`: `iwasawaWeight (p k) = δ(p)^{1/2}` for every `p ∈ P`,
  `k ∈ K`, so the weight does not depend on the chosen factorization.
- `iwasawaWeight_mul_right` (right `K`-invariance), `iwasawaWeight_mul_left`
  (`iwasawaWeight (p g) = δ(p)^{1/2} iwasawaWeight g`), `iwasawaWeight_of_mem` (the
  weight is `1` on `K`).
- `iwasawaWeight_nonneg`, `iwasawaWeight_pos` (no hypothesis on `δ`).
- `isLocallyConstant_iwasawaWeight`, `continuous_iwasawaWeight` for open `K`.

For `Ξ`, with `δ` trivial on `P ∩ K` unless stated otherwise. The hypothesis that `K`
is open is listed for each result that uses it.

- `continuous_iwasawaWeight_mul`, `integrable_iwasawaWeight_mul` (`K` open): the
  integrand `k ↦ iwasawaWeight (k g)` is continuous, hence integrable on `K`.
  Openness of `K` gives the continuity, and compactness of `K` then gives
  integrability.
- `xi_one`: `Ξ(1) = 1`.
- `xi_pos` (`K` open): `Ξ(g) > 0`. The integrand is continuous and everywhere
  positive, and `K` has measure `1`.
- `xi_mul_left` (no hypothesis on `δ` or `K`), `xi_mul_right`, `xi_mul_mul`: `Ξ` is
  bi-`K`-invariant. This is the first assertion of Lemma II.1.1.
- `isLocallyConstant_xi`, `continuous_xi` (`K` open).
- `integral_xi_mul_mul` (`K` open, `G` second countable):
  `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`, Lemma II.1.3. Openness of `K` makes the double
  integrand on `K × K` continuous, hence integrable since `K × K` is compact. Second
  countability of `G` makes the Borel σ-algebra of `K × K` the product σ-algebra, so
  that Fubini's theorem applies.

## Proof notes

Waldspurger proves Lemma II.1.3 with the representation `π`: the vector
`v = ∫_K π(k g₂) e dk` is `K`-invariant, hence `v = Ξ(g₂) e`. The Lean proof works
with the integral formula instead. It writes `Ξ(g₁ k g₂)` as a double integral over
`K × K` and exchanges the integrals (`integral_integral_swap`). For fixed `k'` it
factors `k' g₁ = p k''`. Then `iwasawaWeight (k' g₁ k g₂) = δ(p)^{1/2}
iwasawaWeight (k'' k g₂)`. Left invariance of the Haar measure in `k` turns the
inner integral into `iwasawaWeight (k' g₁) Ξ(g₂)`. Integrating over `k'` gives
`Ξ(g₁) Ξ(g₂)`.

Right `K`-invariance of `Ξ` follows from right `K`-invariance of the weight. Left
`K`-invariance follows from right invariance of the Haar measure on the compact group
`K`.
