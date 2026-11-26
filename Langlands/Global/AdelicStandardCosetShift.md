# Renormalizing shifts on `P₀(F) U_J(𝔸) \ G(𝔸)`

Module `Langlands.Global.AdelicStandardCosetShift` (namespace
`Langlands.Global.StandardConstantTerm`). Fix a connected reductive group `G` over a number
field `F`, a maximal split torus `i : T → G`, a generic cocharacter `ν` and a set `J` of simple
relative roots. Write `Λ₀ = minimalParabolicImage F G i ν` for the image of `P₀(F)` in
`G(𝔸)`, `D₀` for the Library's Borel fundamental domain of `Λ₀`, `U_J` for
`standardUnipotent i ν J` and `L_J` for `standardLevi i ν J`.

## Definitions

- `cosetSubgroup F G i ν J = Λ₀ ⊔ U_J(𝔸)`, a subgroup of `G(𝔸)`. Its left coset space (module
  `Langlands.Analysis.CosetSpaceShift`) is `P₀(F) U_J(𝔸) \ G(𝔸)`.
- `domainWeightedHaar F G i ν W = (Haar|_{D₀}).withDensity W` for a weight
  `W : G(𝔸) → [0, ∞]`.

## Results

- `conj_mem_cosetSubgroup`: let `a ∈ G(𝔸)` commute with every point of `L_J(𝔸)` and satisfy
  `a U_J(𝔸) a⁻¹ ⊆ U_J(𝔸)`. Then `a (Λ₀ ⊔ U_J(𝔸)) a⁻¹ ⊆ Λ₀ ⊔ U_J(𝔸)`. By closure induction it
  suffices to treat generators. A point of `Λ₀` factors as `x c` with `x ∈ Λ₀ ∩ L_J(𝔸)` and
  `c ∈ U_J(F)` (`exists_leviPart_mul`), and `a x c a⁻¹ = x (a c a⁻¹)`.
- `domainWeightedHaar_apply`: the weighted measure of a measurable set `S` is
  `∫_{D₀} 1_S W`.
- `domainWeightedHaar_preimage_mul_left`: let `a` be as above and also satisfy
  `a⁻¹ U_J(𝔸) a ⊆ U_J(𝔸)`. Let `W` be measurable, left invariant under `Λ₀ ⊔ U_J(𝔸)`, with
  `W(g) = κ W(a g)` for all `g`. Then for every measurable set `B` that is a union of cosets of
  `Λ₀ ⊔ U_J(𝔸)`, the weighted measure of `a⁻¹ B` is `κ c(a)` times that of `B`, where
  `c(a) = mulEquivHaarChar (conjPoints F G a ha ha')` is the factor by which conjugation by
  `a` scales Haar measure on `U_J(𝔸)`. The integrand `1_B(a g) W(g)` equals `κ φ(a g)` with
  `φ = 1_B W` invariant, and the translation formula `setLIntegral_mul_left_eq` (module
  `Langlands.Global.AdelicSplitComponentTranslation`) gives `∫_{D₀} φ(a g) = c(a) ∫_{D₀} φ`.
- `standardRenormalizingShift`: with in addition `κ > 0` and a measurable real function
  `ht` on `G(𝔸)`, left invariant under `Λ₀ ⊔ U_J(𝔸)`, with `ht(a g) = ht(g) + 1`, left
  translation by `a` on `P₀(F) U_J(𝔸) \ G(𝔸)` with height induced by `ht` is an
  `L2RenormalizingShift` of the pushforward of `domainWeightedHaar F G i ν W`, with factor
  `√(κ c(a))`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §7.5, pp. 218–219 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). In the application after the
Corollary on p. 218, the renormalizing transformation `σ_α` is left translation by `a_α` on
the relative Siegel domain in `P₀(F) U(𝔸) \ G(𝔸)`, the measure is `w_λ⁻² dx`, and the constant
is `c_α = δ_P(a_α)^{1/2} e^{⟨λ, H₀(a_α)⟩}`. Here the measure is pushed forward from the
fundamental domain of `P₀(F)` in `G(𝔸)`, the weight scaling `κ` is a hypothesis (for
`W = e^{-2⟨λ, H₀⟩}` one has `κ = e^{2⟨λ, H₀(a)⟩}`), and the modulus enters as the Haar factor
`c(a)` of conjugation on `U_J(𝔸)`; this module does not compare `c(a)` with `δ_P(a)`. The
hypotheses on `a` hold for points of the split component of `L_J`
(`StandardParabolicFamily.splitComponent_commute_standardLevi`,
`splitComponent_conj_mem`, `splitComponent_conj_inv_mem`).
