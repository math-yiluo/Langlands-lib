# Constant terms as integrals over a relatively compact fundamental domain

Let `j : U ⟶ G` be a closed immersion of a smooth connected unipotent group over a number field.
The module `Langlands.Global.AdelicUnipotentFundamentalMeasure` represents the normalized constant
term along `U` by a probability measure on `U(𝔸)` concentrated on a compact set, and deduces a bound
for constant terms of families over an arbitrary measure space.

- `exists_unipotentFundamentalMeasure`: there are a probability measure `ν` on the adelic points of
  `U` (as a subgroup of `G(𝔸)`) and a compact set `C` with `ν(Cᶜ) = 0` such that for every
  continuous left `U(F)`-invariant function `f` on `G(𝔸)` and every `x`,
  `subgroupConstantTerm F j f x = ∫ f(h x) dν(h)`. The measure is the Haar measure of `U(𝔸)`
  restricted to a relatively compact fundamental domain `s` of `U(F)`
  (`LeftCosetSpace.relativelyCompactFundamentalDomain`) and normalized so that the quotient map is
  measure preserving onto `normalizedRationalQuotientHaarMeasure`; then `C` is the closure of `s`.
- `exists_lintegral_enorm_subgroupConstantTerm_le`: there is a compact set `C` of points of `U(𝔸)`
  such that for every family `f o` of continuous left `U(F)`-invariant functions, jointly
  measurable, over an arbitrary measure space `(Ω, m)`,
  `∫_Ω ‖(f o)_U(x)‖ dm ≤ sup_{h ∈ C} ∫_Ω ‖f o (h x)‖ dm`.
  This is `lintegral_lintegral_le_mul_iSup_of_ae` for the measure `ν`, with a countable dense
  subset of `C` detecting vanishing.
