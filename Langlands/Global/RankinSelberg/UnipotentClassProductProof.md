# Proof of premise B: products over the classes `unipotentIntegralClasses`

This module proves `Langlands.Global.RankinSelbergGlobal.UnipotentClassProductStatement`,
premise B of the published reduction `ArchimedeanFactorizationReduction`. The
main theorem is

```
theorem Langlands.Global.RankinSelbergGlobal.UnipotentClass.unipotentClassProductStatement :
    UnipotentClassProductStatement.{u}
```

It uses only the standard axioms.

**The statement.** Fix a number field `F`, `t : ℕ` and a finite set `S` of finite places. Fix
quotient measure data `DR v`, `DC w` at the real and complex places (the Library's
`QuotientMeasureData`: a quotient measure compatible with Haar measures on `GL_(t+1)` and on
`N_(t+1)`, the latter right invariant). Fix measures `μS v` on `N_(t+1)(F_v) \ GL_(t+1)(F_v)`,
`v ∈ S`, satisfying `IsCompatiblePadicQuotientMeasure`. Then there is `C ≠ 0` such that, for all
functions `fR v`, `fC w`, `fS v` on the local quotients,
`∫_(unipotentIntegralClasses F (t+1) S) ∏_v fR v (q_v) ∏_w fC w (q_w) ∏_(v ∈ S) fS v (q_v) dq`
equals `C ∏_v ∫ fR v ∏_w ∫ fC w ∏_(v ∈ S) ∫ fS v`. Here `dq` is `whittakerQuotientMeasure` and
`q_v` are the Library's local projections. No integrability or measurability is assumed: every
step below is an identity of Bochner integrals valid for all functions.

Provenance: internal. The argument is the standard one: the domain is a homogeneous space of a
semilocal group, invariant measures on it are unique up to a scalar, and the product measure
is invariant. It is the measure-theoretic content of the factorization in Cogdell 2004, proof of
Theorem 4.1, pp.219-220.

The proof uses two helper modules: `Langlands.Analysis.Local.LeftQuotientProduct` (left quotients
of product groups) and `Langlands.Global.RankinSelberg.UnipotentClassDecomposition` (the
semilocal group `𝒢`, its unipotent subgroup `𝒩` and the open embedding
`classMap : 𝒩 \ 𝒢 → N_m(𝔸) \ GL_m(𝔸)` with image `unipotentIntegralClasses`). The notation
follows the latter. All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.UnipotentClass`.

## 1. Generic lemmas

- `gl_secondCountable`: `GL_n(R)` is second countable for a second countable topological ring
  `R` (it embeds into `M_n(R) × M_n(R)ᵐᵒᵖ`).
- `isMulRightInvariant_of_compactSpace`: every Haar measure on a compact second countable group
  is right invariant. The right translate of a Haar measure is a Haar measure, hence a scalar
  multiple of it (Mathlib's `isMulLeftInvariant_eq_smul`). Comparing the finite nonzero masses of
  the whole group shows that the scalar is one. The proof copies the Library's
  `isMulRightInvariant_of_compactOpenCover`, with the whole group as the compact open subgroup.
- `prod_ne_zero_of_ne_zero`, `pi_ne_zero_of_ne_zero`: products of nonzero measures are nonzero.

## 2. The pulled-back measure `ν₁`

The module provides local instances. `𝒢 = SemilocalGL F m S` is Hausdorff, locally compact and
second countable, because the embedding `Ψ` of `UnipotentClassDecomposition` is an open embedding
into `GL_m(𝔸)`. The quotient `𝒩 \ 𝒢` is Hausdorff (`𝒩` is closed), locally compact and second
countable, with its Borel σ-algebra.

- `classMeasure F m S = ν₁` is `Measure.comap classMap (whittakerQuotientMeasure F m)`.
- `setIntegral_unipotentIntegralClasses`: for every `f`,
  `∫_(unipotentIntegralClasses) f = ∫ f ∘ classMap dν₁`. This holds because `classMap` is a
  measurable embedding with range `unipotentIntegralClasses` (`range_classMap`), and
  `map classMap ν₁ = whittakerQuotientMeasure.restrict (range classMap)`.
- `classMeasure_regular`: `ν₁` is finite on compact sets (`IsFiniteMeasureOnCompacts.comap'`,
  using that `whittakerQuotientMeasure` is regular, Library `WhittakerQuotientScaling`). Hence it
  is regular on the second countable locally compact space `𝒩 \ 𝒢`.
- `whittakerQuotientMeasure_ne_zero_of_isOpen`: nonempty open sets have positive
  `whittakerQuotientMeasure`. Some compact set has positive measure, and finitely many right
  translates of the open set cover it. Right translations preserve the measure (Library
  `measurePreserving_rightTranslate`). The argument is that of the Library's
  `IsCompatible.isOpenPosMeasure`. Hence `classMeasure_ne_zero`, since the range of `classMap`
  is open and nonempty.
- `classMeasure_rightTranslate`: right translation by `g ∈ 𝒢` preserves `ν₁`. By
  `classMap_rightTranslate`, `classMap` intertwines it with right translation by `Ψ g`. Hence
  the image under `classMap` of the preimage of `s` is the preimage, under right translation by
  `Ψ g`, of the image of `s`, and `whittakerQuotientMeasure` is invariant.

## 3. Unimodularity of `𝒩`

- `unipotentProductEquiv`: `𝒩 ≃ₜ* ((∏_v N(ℝ) × ∏_w N(ℂ)) × (∏_(v ∈ S) N(F_v) × N_K))`, where
  `N_K = awayUnipotent` is compact (`isClosed_awayUnipotent`: it is the preimage of `𝒩` under
  `k ↦ (1, (1, k))`).
- `completionUnipotentHaar`: the Library's `unipotentHaar` over the completion `F_v`, using the
  valuation and local-field structure of `CompletionPadic.topologicalData v`. It is a Haar
  measure and right invariant (Library `unipotentHaar_isMulRightInvariant`).
- `semilocalUnipotent_haar_rightInvariant`: Haar measure on `𝒩` is right invariant. The product
  of the right-invariant Haar measures `(DR v).unipotentHaar`, `(DC w).unipotentHaar`,
  `completionUnipotentHaar` and Haar measure on the compact group `N_K` is a right-invariant Haar
  measure on the product. `isMulRightInvariant_of_continuousMulEquiv` from `LeftQuotientProduct`
  then transfers right invariance to `𝒩`.

## 4. The product measure `ν₂`

- `quotientCoordinates F m S = Θ : 𝒩 \ 𝒢 ≃ₜ Coordinates F m S`, where
  `Coordinates = (∏_v Q_v × ∏_w Q_w) × (∏_(v ∈ S) Q_v × Y)` with the local quotients
  `Q_v = N(F_v) \ GL(F_v)` and `Y = N_K \ K^S`. `Θ` is built from `leftQuotientProdHomeomorph`
  and `leftQuotientPiHomeomorph`. `quotientCoordinates_mk` gives `Θ [x] = ([x_v])_v`, and
  `quotientCoordinates_rightTranslate` shows that `Θ` turns right translation by `g` into the
  product of the local right translations. Both hold by `rfl` on representatives.
- `awayQuotientMeasure = ρ_Y` is the image of Haar measure of the compact group `K^S` in `Y`. It
  is finite, nonzero (`awayQuotientMeasure_univ_toReal_pos`) and invariant under `K^S`
  (`awayQuotientMeasure_rightTranslate`, using right invariance of Haar measure on `K^S`).
- `productMeasure = P` is the product of `Measure.pi (DR · ).measure`,
  `Measure.pi (DC · ).measure`, `Measure.pi mS` and `ρ_Y`. Here `mS v` are quotient measures at
  the places of `S` for the completion topology (Section 6).
- `realQuotientProjection_classMap_eq` and its complex and finite analogues: the Library's
  local projections of `classMap p` are the coordinates of `Θ p`. This follows from the
  corresponding lemmas of `UnipotentClassDecomposition` on representatives.

## 5. The core theorem

`unipotentClassProduct_core` proves the statement for quotient measures `mS v` at the places of
`S` that are nonzero, regular and invariant under right translations, for the completion
topology. The proof:

1. The local measures are regular. They are σ-finite (locally finite on second countable
   locally compact spaces), so `P` is a nonzero locally finite measure.
2. `ν₂ := map Θ⁻¹ P` is finite on compact sets (`IsFiniteMeasureOnCompacts.map` for the
   homeomorphism `Θ⁻¹`). It is therefore regular and nonzero. It is invariant under right
   translations by `𝒢`, by `measurePreserving_map_symm_of_conj` from `LeftQuotientProduct`
   applied to the product of the local measure-preserving maps (`MeasurePreserving.prod`,
   `measurePreserving_pi`, the right invariance in `IsCompatible`, and
   `awayQuotientMeasure_rightTranslate`).
3. The Library's `QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient`, with
   `G = 𝒢`, `H = 𝒩` (closed) and `μH` = Haar measure on `𝒩` (right invariant by Section 3), gives
   `c > 0` with `ν₁ = c • ν₂`.
4. For every `f`, `∫_(unipotentIntegralClasses) f = c ∫ f(classMap(Θ⁻¹ z)) dP(z)`
   (Section 2, `integral_smul_measure`, `integral_map_equiv`).
5. By Section 4, the integrand `f(classMap(Θ⁻¹ z))` of premise B is
   `(∏_v fR v (z_v) ∏_w fC w (z_w)) · (∏_(v ∈ S) fS v (z_v) · 1)`. Mathlib's `integral_prod_mul`
   (three times) and `integral_fintype_prod_eq_prod` (three times) split the integral into the
   local integrals and the factor `∫ 1 dρ_Y = ρ_Y(Y)`. Both lemmas hold for all functions.
6. The constant is `C = c · ρ_Y(Y) > 0`.

## 6. Change of topology at the places of `S`

The measures `μS v` of premise B live on the quotient for the canonical topology of the p-adic
field `padicField v`. The groups `GL_m(F_v)` of `UnipotentClassDecomposition` carry the
completion topology. The Library's `CompletionPadic.completion_topology_eq v` says that the two
topologies are equal.

- `QuotientMeasureFacts K n c` says that there is a nonzero regular right-invariant measure on
  `N_(n+1)(K) \ GL_(n+1)(K)` whose integrals are given by `c`.
- `quotientMeasureFacts_congr`: this only depends on the topology (by `cases` on the equality of
  topologies).
- `exists_completion_quotientMeasure`: for the canonical topology, `μS v` itself witnesses
  `QuotientMeasureFacts` with `c = padicQuotientIntegral (padicField v) (μS v)`. The three
  properties are fields of the `IsCompatible` structure in `IsCompatiblePadicQuotientMeasure`,
  and the integral identity holds by `rfl`. Transporting gives a measure `mS v` for the
  completion topology with the same integrals.

## 7. The main theorem

`unipotentClassProductStatement` chooses the measures `mS v` of Section 6, applies the core
theorem, and rewrites `∫ fS v d(mS v)` as `padicQuotientIntegral (padicField v) (μS v) (fS v)`.
