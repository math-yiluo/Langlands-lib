# Finite Haar measure of adelic Siegel sets with an open-subgroup Iwasawa input

This module proves one theorem,
`Langlands.Global.AdelicSiegelFactors.measure_weakSiegelProduct_lt_top_of_openSubgroup`.
It is a variant of the published
`siegelProductFiniteMeasureStatement_of_inputs` in
`Langlands/Global/AdelicSiegelMeasureReduction.lean`, and its proof is a copy of that proof
with one step changed.

The published theorem assumes the Iwasawa decomposition `P(𝔸_F) K = G(𝔸_F)`
(`IsParabolicIwasawaCompact`). Here that hypothesis is replaced by an open subgroup `H₁`
with `K ≤ H₁ ⊆ P(𝔸_F) K`. This weaker input can be built without a finite-place Iwasawa
decomposition (`Langlands/Global/AdelicOpenIwasawaCompact.lean`). The module is internal
supporting material for the finite-volume proof, and its mathematical content is that of the
published reduction. The sources are those of `AdelicSiegelMeasureReduction.md`: Getz–Hahn
§3.6 and Borel, *Reduction theory for arithmetic groups*, §1.6 and Lemma 1.9.

## Statement

`measure_weakSiegelProduct_lt_top_of_openSubgroup hU hmod hbox F G hG T i ν T₀ j hsetup C t
H₁ hH₁ hKH₁ hH₁P hcompat` takes:

- `hU : UnipotentRationalQuotientCompactStatement`,
  `hmod : PositiveTorusUnipotentModulusStatement` and `hbox : SimpleRootBoxCompactStatement`.
  These are the three inputs of the published reduction. All three are proved in the Library.
- a number field `F` and an affine group scheme `G` over `Spec F`, locally of finite type and
  connected reductive (`hG`);
- the data `T, i, ν, T₀, j` with `hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j`. Here
  `P = Standard.parabolicScheme i ν ∅` is the canonical minimal parabolic, with Levi
  `M = Standard.leviScheme i ν ∅` and unipotent radical `N = Standard.unipotentScheme i ν ∅`;
- compact factor data `C : CompactFactors F G N M`. This is a compact set `Ω_N ⊆ N(𝔸_F)`, a
  compact set `Ω_M ⊆ M(𝔸_F)¹` and a compact subgroup `K = C.compactSubgroup` of `G(𝔸_F)`;
- a threshold `t : ℝ≥0ˣ`;
- a subgroup `H₁` of `G(𝔸_F)` that is open (`hH₁`) and satisfies `K ≤ H₁` (`hKH₁`) and
  `H₁ ⊆ P(𝔸_F) K` (`hH₁P`). Here `P(𝔸_F)` is the range of the adelic map of
  `Standard.parabolicHom i ν ∅`;
- `hcompat : IsPositiveTorusCompatible F G T i ν T₀ j K`: every element of `K ∩ P(𝔸_F)`
  commutes with the positive torus `A_{T₀}`.

The conclusion is that the trace on `G(𝔸_F)¹` of the weak Siegel product

  `weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t = Ω_N Ω_M A_{T₀}(t) K`

has finite measure for `Measure.haar` on `normOneSubgroup F G`. Here `A_{T₀}(t)` is the weak
simple-root chamber `PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`.

## Proof

Write `H = G(𝔸_F)¹`. As in the published proof:

- `Q`, `M`, `U` and `K` are `P(𝔸_F)`, `M(𝔸_F)`, `N(𝔸_F)` and `K`, read as subgroups of `H`.
  The first three are closed and `K` is compact.
- `Q = M ⋉ U`, with a continuous Levi projection obtained from the scheme-theoretic Levi
  retraction (`exists_standardLeviPart`, `IsSemidirectDecomposition.of_retraction`).
- The positive torus enters through `a = positiveMapNormOneOfDerived`. It takes values in
  `M`, commutes with `M`, and commutes with `K ∩ Q` by `hcompat`.
- `λ_α = |α|` for the simple relative roots `α`. The box is compact by `hbox`, and the
  exponents `e` satisfy `∏ λ_α^{e_α} ≤ δ_U(a)` by `hmod`. These are word for word the
  published steps.

The one changed step is the saturated-set bound needed by
`SiegelSetMeasure.measure_mul_chamber_mul_lt_top`. That bound asks for a measure `μ'` on `H`
and a constant `c` with `μ'(S) ≤ c μ_Q(S ∩ Q)` for every measurable right `K`-saturated
`S ⊆ H`.

1. Let `H₁' = H₁ ∩ H`, an open subgroup of `H` containing `K`. Every `g ∈ H₁'` is `p k` with
   `p ∈ P(𝔸_F)` and `k ∈ K`, by `hH₁P`. Since `K ≤ H`, also `p = g k⁻¹ ∈ H`, so `p ∈ Q`.
2. `CompactFactorization.exists_measure_inter_mul_eq_of_isOpen`
   (`Langlands/Analysis/Local/OpenCompactFactorizationHaar.lean`), applied in `H` to `Q`, `K`
   and `H₁'`, gives `c` with `haar(S ∩ Q H₁') = c μ_Q(S ∩ Q)` for every such `S`.
3. Take `μ' = haar.restrict (Q H₁')`. The set `Q H₁'` is open, hence measurable, so
   `μ'(S) = haar(S ∩ Q H₁') = c μ_Q(S ∩ Q)`.

The abstract bound then gives `μ'(Ω_U Ω_M a(chamber) K) < ∞`. Every element of
`Ω_U Ω_M a(chamber) K` is `u m a(x) k` with `u m a(x) ∈ Q` and `k ∈ K ≤ H₁'`, so this set lies
in `Q H₁'`. On it `μ'` agrees with `haar` (`Measure.restrict_eq_self`). Finally, the trace on
`H` of the weak Siegel product lies in `Ω_U Ω_M a(chamber) K`, by the same factor-by-factor
argument as in the published proof (`mem_productSet_iff`).
