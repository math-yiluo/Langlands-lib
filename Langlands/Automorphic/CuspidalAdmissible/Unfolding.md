# Bounded multiplicity and quotient integrals

Module: `Langlands.Automorphic.CuspidalAdmissible.Unfolding`. Provenance: internal; this is
the standard unfolding inequality for a discrete subgroup, used in the proof of joint
admissibility of unitary cuspidal realizations.

## Generic statement (namespace `Langlands.Global.LeftCosetSpace`)

`lintegral_le_mul_discreteQuotientMeasure Γ hΓ ν A hA t ht htA M hmult f hf`: let `H` be a
second-countable topological group with Borel structure, `Γ` a discrete subgroup, `ν` a
left-invariant measure, `A` a measurable set of the quotient `Γ \ H`, `t ⊆ H` measurable with
`[x] ∈ A` for `x ∈ t`, and suppose every orbit meets `t` in at most `M` points:
`#{γ ∈ Γ : γ x ∈ t} ≤ M` (as an extended natural number, `Set.encard`). Then for every
measurable `f ≥ 0` on the quotient,
`∫_t f([x]) dν(x) ≤ M · ∫_A f d(discreteQuotientMeasure Γ hΓ ν)`.

Proof: with the Library's Borel fundamental domain `s`, the fundamental-domain identity
`IsFundamentalDomain.lintegral_eq_tsum''` writes `∫_H 1_t f([x])` as `∫_s ∑_γ 1_t(γ x) f([x])`;
the sum is `#{γ : γ x ∈ t} · f([x]) ≤ M · 1_A([x]) f([x])` (`tsum_subtype`,
`ENNReal.tsum_set_const`); the quotient measure is the pushforward of `ν|_s`.

## The actual general linear quotient (namespace `Langlands.Automorphic.OperatorDeterminantSlice`)

`lintegral_le_mul_quotient F n A hA t ht htA M hmult h hh`: for the actual quotient
`Quotient F n`, its measure `quotientHaarMeasure F n`, a measurable `t ⊆ AdelicGL F n` lying
over `A` (`point F n x ∈ A`), and `#{γ : RationalGL F n | rational γ * x ∈ t} ≤ M` for every
`x`, we get `∫_t h(point x) d(matrixHaarMeasure) ≤ M ∫_A h d(quotientHaarMeasure)`.
The proof transports to the group-scheme points through `adelicHomeomorph`; a subgroup
element `γ` corresponds injectively to the rational matrix `rationalEquiv` of its chosen
preimage (`adelicHomeomorph_rational`), which bounds the multiplicity there.

`lintegral_quotient_le_cover F n A hA t ht hcover h hh` (**covering**): if every
`x ∈ GL_n(𝔸)` with `point F n x ∈ A` has a rational translate `rational γ * x ∈ t`
(`t` measurable), then for measurable `h ≥ 0`,
`∫_A h d(quotientHaarMeasure) ≤ ∫_t h(point x) d(matrixHaarMeasure)`. This is the Library
inequality `LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le` for the group-scheme
points, transported through `adelicHomeomorph` (a covering rational matrix gives the covering
subgroup element `rational r`, `r = rationalEquiv⁻¹ γ`), and the pushforward description of
`matrixHaarMeasure` (`lintegral_map`).
