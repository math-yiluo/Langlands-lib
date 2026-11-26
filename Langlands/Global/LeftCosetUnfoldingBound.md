# Integrals over `Γ \ H` bounded by integrals over a covering set

Module `Langlands.Global.LeftCosetUnfoldingBound`, namespace `Langlands.Global.LeftCosetSpace`.

For a discrete subgroup `Γ` of a second-countable topological group `H`, a measure `ν` on `H`
invariant under left translation by `Γ`, and a measurable left `Γ`-invariant function
`f : H → [0, ∞]`, the module proves

`∫_{Γ \ H} f(y.out) d(discreteQuotientMeasure Γ hΓ ν) ≤ ∫_Y f dν`

for every set `Y ⊆ H` whose left `Γ`-translates cover `H`. This is the elementary form of the
unfolding inequalities of reduction theory. (Lapid, *On the Harish-Chandra Schwartz space of
G(F)\G(A)*, ESI preprint 2403, §1, inequality (2), printed p. 5 (PDF p. 6), is a variant in
which the integral on the right is over `P₀(F) \ 𝔰` for a Siegel domain `𝔰`.) The statement here is internal and derived only from the
Library's construction of `discreteQuotientMeasure` and Mathlib's fundamental-domain API. Its adelic use is in
`Langlands/Global/AdelicSiegelDominatedIntegrabilityProof.lean`.

## Declarations

- `exists_out_mk_eq_mul Γ g`: the chosen representative `(mk Γ g).out` of the coset of `g` is
  `γ g` for some `γ ∈ Γ`. It follows from `Quotient.out_eq` and `mk_eq_mk_iff`.
- `apply_out_mk Γ hinv g`: a left `Γ`-invariant function takes the same value at `g` and at the
  representative of its coset.
- `measurable_comp_out Γ hf hinv`: for measurable left `Γ`-invariant `f`, the function
  `y ↦ f(y.out)` on `Γ \ H` is measurable. Its pullback along `mk Γ` is `f` itself, and the
  σ-algebra of `Γ \ H` is the quotient σ-algebra (`measurable_from_quotient`).
- `lintegral_comp_out_le_setLIntegral` (**unfolding inequality**). Hypotheses: `Γ` discrete,
  `[SMulInvariantMeasure Γ H ν]`, `f` measurable and left `Γ`-invariant, and
  `∀ g, ∃ γ ∈ Γ, γ g ∈ Y`. The set `Y` need not be measurable.

  *Proof.*
  1. `discreteQuotientMeasure Γ hΓ ν` is the pushforward of `ν` restricted to the chosen Borel
     fundamental domain `D` (`quotientMeasure`). By `lintegral_map` and `apply_out_mk`, the left
     side is `∫_D f dν`.
  2. `D` is a fundamental domain for `Γ` (`isFundamentalDomain`), and `Γ` is countable
     (`countable_of_isDiscrete`). Mathlib's `IsFundamentalDomain.setLIntegral_eq_tsum'` gives
     `∫_Y f = ∑_{γ ∈ Γ} ∫_{γY ∩ D} f(γ⁻¹ x) dν(x) = ∑_γ ∫_{γY ∩ D} f`, using invariance of `f`.
  3. Every `x ∈ D` has some `γ` with `γ x ∈ Y`, so `D ⊆ ⋃_γ (γ⁻¹ Y ∩ D)`. Hence
     `∫_D f ≤ ∑_γ ∫_{γY ∩ D} f` (`lintegral_mono_set`, `lintegral_iUnion_le`), which is
     `∫_Y f` by step 2.

The module uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
