# Comparing two compact factors through modular-equivariant functions

Module `Langlands.Analysis.Local.CompactFactorizationModularComparison` contains no adelic or
algebraic-group content. Its two theorems are stated for abstract groups and are in the
namespace `Langlands.CompactFactorization`, shared with `CompactFactorizationHaar`,
`CompactFactorizationIntegral` and `CompactFactorizationBochner`.

## Setting

`G` and `P` are second countable, locally compact, Hausdorff topological groups with their
Borel σ-algebras, and `ι : P →* G` is a group homomorphism that is a closed embedding. `K`,
`K₁`, `K₂` are compact subgroups of `G` with `G = ι(P) K`, that is
`∀ g, ∃ q k, k ∈ K ∧ ι q * k = g`. The modular character `Δ_P` is Mathlib's
`MeasureTheory.Measure.modularCharacter` of `P`: `map (· * q) μ = Δ_P(q) • μ` for a left Haar
measure `μ` (`map_right_mul_eq_modularCharacterFun_smul`).

## `exists_pos_eq_smul_map_hom_mul_prod`

For a left Haar measure `μ` on `G`, left Haar measures `μP` on `P` and `μK` on `K`, there is
`c > 0` with `μ = c • map (fun (q, k) => ι q * k) (μP × μK)`.

Proof. `Q = ι(P)` is a closed subgroup of `G` (`IsClosedEmbedding.isClosed_range`). The
corestriction `ι' : P → Q` is a continuous surjective closed embedding, so `map ι' μP` is a left
Haar measure on `Q` (`Measure.isHaarMeasure_map`). The published
`exists_pos_eq_smul_map_mul_prod` of `CompactFactorizationHaar` gives
`μ = c • map (fun (q, k) => q * k) ((map ι' μP) × μK)`, and
`(map ι' μP) × μK = map (ι' × id) (μP × μK)` (`Measure.map_prod_map`) turns this into the
claim.

## `exists_lintegral_compact_eq_of_modular`

For left Haar measures `μ₁` on `K₁` and `μ₂` on `K₂` there is `c > 0` such that every measurable
`φ : G → [0, ∞]` with `φ(ι(q) g) = Δ_P(q) φ(g)` for all `q`, `g` satisfies

`∫_{K₁} φ dμ₁ = c ∫_{K₂} φ dμ₂`.

The constant is chosen before `φ`.

Proof. Fix the Haar measures `μ` on `G` and `μP` on `P` and apply the previous theorem to `K₁`
and `K₂`: `μ = cᵢ • map (ι q * k) (μP × μᵢ)`. By Tonelli (`lintegral_prod_symm`), for every
measurable `f ≥ 0` on `G`,

`∫_G f dμ = cᵢ ∫_{Kᵢ} (∫_P f(ι(q) k) dμP(q)) dμᵢ(k)`.

Choose a compact neighbourhood `W` of `1` in `G` and put `B = W K₁`, a compact set, and
`b(g) = ∫_P 1_B(ι(q) g) dμP(q) = μP({q | ι(q) g ∈ B})`.

- `b` is measurable (`Measurable.lintegral_prod_left'`).
- `b(g) < ∞`: the set `{q | ι(q) g ∈ B}` is the preimage under `ι` of the compact set `B g⁻¹`,
  hence compact because `ι` is a closed embedding.
- `b(g) > 0`: write `g = ι(q₀) k₀` with `k₀ ∈ K₁`. The set contains `{q | ι(q q₀) ∈ W}`, a
  neighbourhood of `q₀⁻¹`, which has positive Haar measure.
- `b(ι(q₀) g) = Δ_P(q₀) b(g)`: substitute `q ↦ q q₀` and use
  `map (· * q₀) μP = Δ_P(q₀) • μP`.

Put `f = 1_B · φ · b⁻¹`. It is measurable, and for every `g` the factors `Δ_P(q)` of `φ` and `b`
cancel in the inner integral:

`∫_P f(ι(q) g) dμP(q) = (φ(g) / b(g)) ∫_P 1_B(ι(q) g) dμP(q) = φ(g)`.

So `c₁ ∫_{K₁} φ dμ₁ = ∫_G f dμ = c₂ ∫_{K₂} φ dμ₂`, and `c = c₂ / c₁`.

The argument does not use continuity or semicontinuity of `φ`, nor a measure on the quotient
`ι(P) \ G`: the test function `f` is built from `φ` directly.

## Use

`Langlands.Global.AdelicFiniteCompactPairingComparisonProof` applies the second theorem to
`ι = map F P G p : P(𝔸) → G(𝔸)` for a standard parabolic `P` and two Iwasawa compacts, where
`Δ_P` is the modulus `δ_P` of `P(𝔸)`. This is the comparison of the Haar probabilities of two
compacts in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.1.13,
printed p. 18 (registered as `moeglin-waldspurger-1995-spectral-decomposition`), for functions
on `G(𝔸)` that transform under `P(𝔸)` by `δ_P`.
