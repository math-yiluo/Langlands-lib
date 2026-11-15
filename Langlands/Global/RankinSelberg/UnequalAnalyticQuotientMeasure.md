# Automorphisms of discrete left quotients and their quotient measures

Provenance: internal. This module is a generic supporting lemma module for the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
The proof needs two changes of variables on quotients `Γ \ H` by group automorphisms that
carry `Γ` onto itself: conjugation by a rational block matrix on `Y(F) \ Y(𝔸)` (left
`GL_m(F)`-invariance of the projected cusp form), and transpose inverse on
`GL_m(F) \ GL_m(𝔸)` (the functional equation). The Library's comparison
`integral_comp_rationalQuotientIso` requires a compact quotient, which is not available for
`Y(F) \ Y(𝔸)` in the Library, so this module proves the needed facts directly from the
fundamental-domain construction of the Library quotient measures
(`Langlands.Global.LeftCosetSpace.quotientMeasure`, `discreteQuotientMeasure`).

Notation: `H` is a group, `Γ` a subgroup, `α : H ≃* H` with `α x ∈ Γ ↔ x ∈ Γ` for all `x`.
All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.

## Declarations

- `symm_mem_iff`: `α⁻¹` also satisfies `α⁻¹ x ∈ Γ ↔ x ∈ Γ`.
- `cosetMap Γ α hα`: the map `Γ x ↦ Γ α(x)` of `Γ \ H`, defined with
  `LeftCosetSpace.lift` (well defined because `α (γ x) = α(γ) α(x)` with `α(γ) ∈ Γ`).
  `cosetMap_mk` is its defining equation; `cosetMap_symm_cosetMap` and
  `cosetMap_cosetMap_symm` show that the map induced by `α⁻¹` is its inverse.
- `measurable_cosetMap`: measurable when `α` is (`measurable_from_quotient`).
- `cosetMeasurableEquiv Γ α hα hm hm'`: the induced map as a measurable equivalence, for
  `α` and `α⁻¹` measurable; `coe_cosetMeasurableEquiv` identifies its underlying function.
- `map_cosetMap_quotientMeasure` (**transport of quotient measures**): the induced map
  pushes `quotientMeasure Γ ν s` (the image of `ν|_s` in `Γ \ H`) to
  `quotientMeasure Γ (α_* ν) (α⁻¹)⁻¹(s)`. Proof: the induced map composed with the
  projection is the projection composed with `α`, so the pushforward is the image of
  `α_*(ν|_s)`, and `α_*(ν|_s) = (α_* ν)|_{α(s)}` (`MeasurableEquiv.restrict_map`).
- `isFundamentalDomain_preimage_symm`: for discrete `Γ` in a second-countable topological
  group, `α(D) = (α⁻¹)⁻¹(D)`, with `D` the Library's chosen Borel fundamental domain, is a
  fundamental domain for the left action of `Γ`, for every measure. Proof:
  `IsFundamentalDomain.mk'`; for `x`, the unique `δ ∈ Γ` with `δ α⁻¹(x) ∈ D` gives the
  unique `α(δ)` with `α⁻¹(α(δ) x) ∈ D`.
- `map_cosetMap_discreteQuotientMeasure` (**scaling**): if `Γ` is discrete, `ν` is
  `Γ`-invariant and `α_* ν = c ν`, then the induced map pushes
  `discreteQuotientMeasure Γ hΓ ν` to `c` times itself. Proof: the transport lemma, the
  hypothesis, `quotientMeasure_smul`, and independence of the fundamental domain
  (`discreteQuotientMeasure_eq`) applied to `α(D)`.
- `map_inv_measure_univ_smul` (**normalized measures are preserved**): if a measurable
  equivalence `f` satisfies `f_* μ = c μ`, then it preserves `(μ univ)⁻¹ μ`. Proof:
  evaluating on `univ` gives `μ univ = c μ univ`. If `μ univ = 0` then `μ = 0`; if
  `μ univ = ∞` then `(μ univ)⁻¹ = 0`; otherwise `c = 1`. In each case both sides agree.
  This applies to the Library's `normalizedRationalQuotientHaarMeasure`, which is
  `quotientMassNormalizer • rationalQuotientHaarMeasure` with
  `quotientMassNormalizer = (rationalQuotientHaarMeasure univ)⁻¹`.
- `map_haar_eq_smul φ`: for a topological automorphism `φ` of a locally compact group,
  `φ_* haar = (mulEquivHaarChar φ)⁻¹ haar` (Mathlib `mulEquivHaarChar_smul_map`).
The generic involution result is imported from `Analysis/Local/InvolutiveHaarCharacter`
under its existing name
`Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.mulEquivHaarChar_eq_one_of_involutive`.
If `φ ∘ φ = id`, multiplicativity makes its nonnegative Haar character have square
one, so `mulEquivHaarChar φ = 1`.
