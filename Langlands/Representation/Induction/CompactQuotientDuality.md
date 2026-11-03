# Invariant integrals over a compact quotient and induction duality

Author: Worker 805.

This module supplies the analytic inputs of Casselman's pairing argument for
the smooth dual of a normalized induction from a closed subgroup `P` with
compact quotient `P \ G`. It does not use a decomposition `G = P K`. It has
two parts.

1. A variant `exists_integralDualEquiv_of_pos` of the published
   `Langlands.Induction.exists_integralDualEquiv` (module `CompactPairingDuality`).
   The measure on `K` only has to be positive on open neighbourhoods of `1`.
2. A construction `bruhatMeasure` and the theorem
   `exists_compactQuotient_measure`. They give a measure on `⊤ : Subgroup G`
   whose integral satisfies the scalar hypothesis `hscalar` of part 1 for
   `δ = ` Mathlib's modular character of `P`, whenever `G` is unimodular.

With `K := ⊤`, the measure of part 2 can be fed into part 1. The module states
no new proposition. It is partial progress towards the proof task
`2137e0ce-8d32-43f5-b4ed-79824b68585f`, whose target is
`Langlands.Aubert.General.RationalPointFamily.RationalNaturalInductionDualityStatement`.
The module does not prove that target. Applying it there needs compactness of
`P \ G` and the identity between the modular character of `P` and the square
of the half character used by normalized induction. These are separate
statements in the Library.

## Provenance

Internal. The module states no definition or proposition taken from a source.
Its two definitions are a measurable identification and a measure with a
density, both made for this proof. The mathematics is the standard
Bruhat-function argument for invariant functionals on a quotient `P \ G`,
specialized to compact quotients and written out below. The duality part
follows Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III, section 1 (registered as `casselman-2019-jacquet-module`),
as already formalized by Worker 715 in `CompactPairingDuality`. There `K` is a
good compact subgroup with `G = P K`, which is not available here.

## Conventions

- `Measure.modularCharacter` is Mathlib's modular character. For a Haar
  measure `μ`, `map (· * g) μ = modularCharacter g • μ`.
- `haar` is Mathlib's chosen Haar measure `haarMeasure`. It is regular, so the
  results below need no second countability.
- `LeftQuotient P` is the Library's space of cosets `P x`, with the quotient
  topology.
- The positivity condition used throughout is
  `hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U`.

## Part 1: duality for measures positive near `1`

Sections `Scalar` and `Nondegeneracy` copy the corresponding results of
`CompactPairingDuality` (Worker 715). The only change is that the hypothesis
`[μ.IsOpenPosMeasure]` becomes `hpos`, in the same argument position. The
proofs are otherwise unchanged, except that they call the `_of_pos` variants. Positivity is used in exactly one place: the
open set `{k : K | x₀⁻¹ k x₀ ∈ L}` contains `1`, so it has positive measure.

- `integral_ne_zero_of_doubleCoset_of_pos`. Let `ψ` be `δ`-covariant, equal to
  a constant `c ≠ 0` on `x₀ L` for an open subgroup `L`, and zero off
  `P x₀ L`. If `k ↦ ψ(k x₀)` is integrable, then `∫_K ψ(k x₀) dμ ≠ 0`.
- `integral_dualPairing_right_nondegenerate_of_pos` and
  `integral_dualPairing_left_nondegenerate_of_pos`. These are the two
  nondegeneracy statements for the integral pairing between
  `smoothInduced P (twist χ (σ.comp m))` and
  `smoothInduced P (twist χ ((smoothContragredient σ).comp m))`.
- `exists_integralDualEquiv_of_pos`. This has the hypotheses and conclusion of
  `exists_integralDualEquiv`, except for `hpos`. Its arguments are
  `(P m χ δ K μ)` explicitly, then `hm hχ hδ hcofM hpos hscalar σ hσ hadm`. The
  conclusion gives a `Representation.Equiv` `E` from the smooth contragredient
  of the admissible induction to the induction of the contragredient, with
  `⟨ℓ, f⟩ = ∫_K ⟨E ℓ (k), f (k)⟩ dμ`. `integralDualEquiv_natural` applies to
  this formula without change.

## Part 2: the Bruhat measure

### Section `Modular`

`H` is a topological group.

- `map_mul_right_haar_eq`: `map (· * q) haar = modularCharacter q • haar`. The
  image measure is regular and left invariant, so
  `isMulLeftInvariant_eq_smul_of_regular` applies. Unlike
  `ModularCompactAverage.map_mul_right_eq_modularCharacter_smul`, this needs no
  second countability.
- `integral_mul_right_haar`:
  `∫ f (x q) d haar = modularCharacter q • ∫ f d haar`.
- `modularCharacter_eq_one_of_isCompact`: the modular character is `1` on a
  compact open subgroup `U`. Right translation by `u ∈ U` preserves `U`, and
  `0 < haar U < ∞`. The argument is that of
  `ModularCompactAverage.modularCharacter_eq_one_of_mem`.
- `isLocallyConstant_of_mul_right`: a function invariant under right
  translation by an open subgroup is locally constant.
- `isLocallyConstant_modularCharacter`: the modular character is locally
  constant when a compact open subgroup exists.

### Section `Bruhat`

`integral_bruhat_eq` is the core identity. Let `G` be a Hausdorff topological
group and `P` a closed subgroup. Let `μ` be a left invariant measure on `G`
that is finite on compacts, and `ν` a measure on `P` that is finite on
compacts. The function `Δ : P → ℝ` is continuous with `Δ(p⁻¹) Δ(p) = 1`. Let
`β, β₁ : G → ℝ` be continuous with compact support and normalized by

- `∫_P β₁(p x) Δ(p) dν(p) = 1` for all `x`,
- `∫_P β(p⁻¹ x) dν(p) = 1` for all `x`.

Then `∫ β φ dμ = ∫ β₁ φ dμ` for every continuous `φ : G → ℂ` with
`φ(q x) = Δ(q) φ(x)`.

Proof. Insert the first normalization into `∫ β φ dμ`, which gives
`∫_G ∫_P β(y) φ(y) β₁(p y) Δ(p) dν dμ`. Exchange the integrals with
`integral_integral_swap_of_hasCompactSupport`. The integrand is continuous and
supported in `tsupport β × (P ∩ S)`, where `S` is the compact set
`tsupport β₁ · (tsupport β)⁻¹`. `P ∩ S` is compact because `P` is closed.
For fixed `p`, substitute `y = p⁻¹ x` by left invariance of `μ`. Covariance
gives `φ(p⁻¹ x) = Δ(p⁻¹) φ(x)`, which cancels `Δ(p)`. Exchange back, with the
same support argument for the new integrand. The second normalization then
gives `∫ φ β₁ dμ`. The identity uses no unimodularity. `Δ` is any continuous
function with `Δ(p⁻¹) Δ(p) = 1`, not necessarily a modular character.

### Section `Construction`

`G` is a locally compact, Hausdorff, nonarchimedean group with its Borel
measurable structure. `P` is a closed subgroup with `LocallyCompactSpace P`
and `CompactSpace (LeftQuotient P)`.

- `continuous_modularCharacter_of_isClosed`: the modular character of `P` is
  continuous. A compact open subgroup of `G` meets `P` in a compact open
  subgroup of `P`.
- `modularCharacter_inv_mul_self`:
  `modularCharacter p⁻¹ * modularCharacter p = 1` in `ℝ`.
- `exists_bruhat_functions`. This produces `β₁, β₂ : G → ℝ`, continuous with
  compact support, and an open `W ∋ 1` with `β₂ ≥ 0`, `β₂ > 0` on `W`,
  `∫_P β₁(p x) Δ_P(p) d haar = 1` and `∫_P β₂(p⁻¹ x) d haar = 1`, where
  `Δ_P` is the modular character of `P`. Construction: take a compact open
  subgroup `K₀` of `G` and a finite set `t` with `G = ⋃_{i ∈ t} P i K₀`
  (`exists_finset_doubleCoset_cover`). Let `C = ⋃_{i ∈ {1} ∪ t} i K₀` and let
  `c` be the indicator of `C`. Then `C` is compact and open, contains `1`, is
  right `K₀`-invariant, and meets every coset `P x`. The averages
  `A(x) = ∫_P c(p x) Δ_P(p) dp` and `B(x) = ∫_P c(p⁻¹ x) dp` are positive and
  left `P`-invariant. For `A` this uses `integral_mul_right_haar` on `P`, and
  this is where `δ = Δ_P` is needed. For `B` it uses left invariance. Both
  averages are also right `K₀`-invariant. Set `β₁ = c / A` and `β₂ = c / B`.
  They are locally constant, hence continuous, and supported in `C`.
- `topMeasurableEquiv`: the identity of `G` as a measurable equivalence
  `G ≃ᵐ (⊤ : Subgroup G)`.
- `bruhatMeasure β`: the measure on `⊤ : Subgroup G` that is the image under
  `topMeasurableEquiv` of `haar` with density `x ↦ max (β x) 0`, written
  `Real.toNNReal (β x)` in Lean. This is the entry declaration of the
  contribution. It is a measure on a subgroup because the scalar hypothesis of
  part 1 is stated for a measure on a subgroup `K`.
- `integrable_bruhatMeasure_iff` and `integral_bruhatMeasure`: for measurable
  `β ≥ 0`, integrability and integrals of `k ↦ ψ k` against `bruhatMeasure β`
  are those of `x ↦ β(x) ψ(x)` against `haar`.
- `bruhatMeasure_pos`: if `β` is measurable and positive on an open `W ∋ 1`,
  then `bruhatMeasure β` is positive on every open `U ∋ 1`, since
  `W ∩ U` is open and nonempty.
- `exists_compactQuotient_measure`. Assume moreover
  `hG : ∀ g : G, modularCharacter g = 1`. Then some measure `μ` on
  `⊤ : Subgroup G` is positive on open neighbourhoods of `1`, and the following
  holds. For every locally constant `φ : G → ℂ` with
  `φ(q x) = Δ_P(q) φ(x)` for `q ∈ P` and every `g ∈ G`, the function
  `k ↦ φ(k g)` is `μ`-integrable and `∫ φ(k g) dμ = ∫ φ(k) dμ`. The proof
  takes `μ = bruhatMeasure β₂`. By `integral_mul_right_haar` and `hG`,
  `∫ β₂(x) φ(x g) d haar = ∫ β₂(x g⁻¹) φ(x) d haar`. The function
  `x ↦ β₂(x g⁻¹)` again satisfies the `B` normalization, so
  `integral_bruhat_eq` turns this integral into `∫ β₁ φ d haar`, which does not
  depend on `g`. Integrability holds because the integrand is continuous with
  compact support.

## How the parts combine

Take `δ := fun q => Measure.modularCharacter q` on `P` and `K := ⊤`. The second
conjunct of `exists_compactQuotient_measure` is exactly `hscalar`, and the
first is `hpos`. If `χ : P →* ℂˣ` has open kernel and `χ(q)² = δ(q)`, then
`exists_integralDualEquiv_of_pos` gives the duality equivalence for every
admissible induction.

## Scope and limits

- The measure depends on the choices of `K₀` and `t`. Nothing is claimed about
  uniqueness or normalization.
- `bruhatMeasure β₂` is generally not positive on every nonempty open set. It
  is zero outside `C`. This is why part 1 weakens `IsOpenPosMeasure` to `hpos`.
- Unimodularity of `G` is used only in `exists_compactQuotient_measure`.
  Closedness of `P`, local compactness and the Hausdorff property are used for
  the compact supports and for Haar measure on `P`.
- `LocallyCompactSpace P` is an instance argument. It follows from closedness
  of `P` through Mathlib's `IsClosed.locallyCompactSpace`.
