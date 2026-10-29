# Proof that character-weighted product averaging is surjective

This module proves
`Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageSurjective.{uG, uY}`.
Its type is exactly the published proposition
`Langlands.HarmonicAnalysis.SchwartzBruhat.CharacterAverageSurjectiveStatement.{uG, uY}`
from `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement`.
The two universes stay arbitrary and independent.

The map is the published
`Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverage χ μ`, between the
published Schwartz–Bruhat spaces. By `characterAverage_apply` it is

    characterAverage χ μ α y =
      ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

The domain is the right-associated product `G × (Y × G)`. The measure is
`μ.prod μ`. Both outer character values are inverted. Nothing about the map or
the statement is changed.

All declarations below are in the namespace
`Langlands.HarmonicAnalysis.SchwartzBruhat`.

## Imports

- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement`:
  the target proposition, and through it the published average.
- `Langlands.Representation.Twist.ContinuousCharacterProof`: the published
  `Langlands.isOpen_ker_of_continuous_complex_character`. The kernel of a
  continuous character `G →* ℂˣ` on a nonarchimedean group is open.
- `Langlands.Topology.CompactOpen.NeighborhoodBasis`: the published
  `Langlands.compactOpenSubgroupBasis`. In a nonarchimedean, weakly locally
  compact group, every neighbourhood of `1` contains a compact open subgroup.

## Helper declarations

The proof uses the following local helpers and imported Hecke indicator facts.

- `tripleTensor φ f ψ`, for `φ ψ : SchwartzBruhat G` and `f : SchwartzBruhat Y`.
  It is the test function `(g₁, (y, g₂)) ↦ φ g₁ * f y * ψ g₂` on
  `G × (Y × G)`. Only topologies on `G` and `Y` are assumed.
  - Local constancy: each factor is a locally constant function composed with
    a continuous projection, and products of locally constant functions are
    locally constant (`IsLocallyConstant.comp₂`).
  - Compact support: the function vanishes outside
    `support φ ×ˢ (support f ×ˢ support ψ)`. Each support is compact
    (`Hecke.TestFunction.isCompact_support`) and closed, because the support of
    a locally constant function is clopen (`Hecke.TestFunction.isClopen_support`).
    So this product set is compact and closed, and `HasCompactSupport.intro'`
    applies. The closure of the support is not computed, so no separation
    property of `Y` is needed.
  - `tripleTensor_apply` is the evaluation law, proved by `rfl`.
- `Hecke.HeckeAlgebra.normalizedIndicator μ K hK`, for a measure `μ`, an open subgroup `K` and
  a proof `hK` that `K` is compact. It is
  `((μ.real K : ℂ))⁻¹ • 1_K`, built from the published
  `Hecke.TestFunction.characteristic` of the clopen (`OpenSubgroup.isClopen`)
  compact set `K`. `normalizedCharacteristic_apply` gives its value as the
  indicator of `K` with constant value `((μ.real K : ℂ))⁻¹`.
- `Hecke.HeckeAlgebra.compactOpen_mass_pos`: for a Haar measure `μ` and a compact open
  subgroup `K`, `0 < μ.real K`. The mass `μ K` is positive because `K` is open
  and contains `1` (`IsOpen.measure_pos`). It is finite because `K` is compact
  (`IsCompact.measure_lt_top`). Hence its real value is positive.
- `characterAverage_tripleTensor_normalizedCharacteristic`: the evaluation
  identity. Assume `[IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]`,
  a continuous character `χ`, a Haar measure `μ` with `[SFinite μ]`, and a
  compact open subgroup `K` with `χ g = 1` for all `g ∈ K`. Write `φ` for
  `Hecke.HeckeAlgebra.normalizedIndicator μ K hK`. Then for every `f : SchwartzBruhat Y`,

      characterAverage χ μ (tripleTensor φ f φ) = f.

## Proof of the evaluation identity

Fix `y : Y` and write `c = (μ.real K : ℂ)`, so `c ≠ 0`.

1. **The integrand is an indicator.** For `z = (g₁, g₂)` the integrand is
   `φ g₁ * f y * φ g₂ * ((χ g₁ : ℂ) * (χ g₂ : ℂ))⁻¹`. It equals
   `(K ×ˢ K).indicator (fun _ => c⁻¹ * f y * c⁻¹) z`. If `g₁ ∈ K` and `g₂ ∈ K`,
   both character values are `1` by the kernel hypothesis, so the weight is `1`.
   Otherwise one factor `φ gᵢ` is zero. The four cases are checked separately.
2. **The integral of the indicator.** `K` is open, hence measurable for the
   Borel σ-algebra, and `K ×ˢ K` is measurable for the product σ-algebra.
   Mathlib's `integral_indicator_const` gives the value
   `(μ.prod μ).real (K ×ˢ K) • (c⁻¹ * f y * c⁻¹)`.
3. **The rectangle mass.** `Measure.prod_prod` gives
   `(μ.prod μ) (K ×ˢ K) = μ K * μ K`. It uses only `SFinite μ`. Taking real
   parts (`ENNReal.toReal_mul`) gives `μ.real K * μ.real K`.
4. **Normalization.** The value is `c * c * (c⁻¹ * f y * c⁻¹) = f y`, by
   `field_simp` with `c ≠ 0`.

No right invariance, unimodularity or σ-finiteness of `μ` is used. Left
invariance is not used either. The proof uses only three properties of `μ`:
it is positive on the nonempty open set `K`, finite on the compact set `K`,
and s-finite, which `Measure.prod_prod` requires.

## Proof of the theorem

`characterAverageSurjective` introduces `G`, `Y`, the exact group instances,
`[TopologicalSpace Y]`, `χ`, `μ`, the Haar and s-finiteness instances, and a
target `f : SchwartzBruhat Y`.

1. `isOpen_ker_of_continuous_complex_character` applied to the underlying
   monoid homomorphism of `χ` and its continuity shows that `ker χ` is open. It
   uses `NonarchimedeanGroup G`. So `ker χ` is a neighbourhood of `1`.
2. `compactOpenSubgroupBasis` gives an open subgroup `K` that is compact and
   contained in `ker χ`. It uses `NonarchimedeanGroup G` and local compactness.
   Hence `χ g = 1` for all `g ∈ K`.
3. The preimage is `tripleTensor φ f φ` with `φ = Hecke.HeckeAlgebra.normalizedIndicator μ K hK`.
   The evaluation identity shows that its average is `f`.

The proof uses no unitarity, local constancy or open-kernel premise on `χ`. The
open kernel is derived from continuity and the nonarchimedean hypothesis. The
`T2Space G` instance is not used by the argument.

## Why only a topology on `Y` is needed

`Y` enters only through `f`. Its support is clopen because `f` is locally
constant, and compact because `f` has compact support. That is all the
tensor construction needs. The evaluation identity is pointwise in `y`. No
Hausdorffness, local compactness, total disconnectedness, countability or
nonemptiness of `Y` is assumed or used. If `Y` is empty, the argument still
applies unchanged.

## Source correspondence

J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193, registered as `shalika-1974-multiplicity-one`
(SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`).
Proposition 1.12, printed p.177 (PDF page 8), defines
`β_α(h) = ∫ α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂` and asserts that `α ↦ β_α` is
surjective. The source omits the proof ("similar to Lemma 21 of [11]"). The
correspondence of `U`, `H`, `du`, `χ̄(u₁u₂)` with `G`, `Y`, `μ` and the inverse
of both character factors is recorded in the statement's Markdown.

The argument here is an internal proof of the published, more general
statement. It does not follow the cited Lemma 21, which was not consulted. It
proves only surjectivity. The existence and uniqueness of the distribution `τ`
in Proposition 1.12, translation covariance of the average, Bruhat cell descent
and Shalika invariance are not proved here.

The normalized indicator and positive-mass theorem above are imported from [NormalizedIndicator](../../Representation/Hecke/NormalizedIndicator.md). Their definitions and assumptions are unchanged; this proof supplies the characteristic-function evaluation and product-averaging argument.
