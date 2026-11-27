# Translating the open-cell integrand by small finite adelic matrices

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellFiniteTranslation`, namespace
`Langlands.Global.CuspidalPairEisenstein.FiniteTranslation`.

Let `Z` be an adelic `(t + 1) × (r + 1)` matrix whose archimedean component is `0` and whose
components are integral at every finite place. The module proves that the open-cell integrand
`openCellIntegrand ψ φ s` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) is
unchanged by `Y ↦ Y + Z` under two conditions, and gives sufficient conditions for both.

## Content

- **`exists_finiteBox_eq_one`**: for a continuous `ψ : AddChar (Adeles F) ℂ` there are a
  finite set `T_ψ` of finite places and `a : ∀ v, F_v` with `a_v ≠ 0` and `|a_v|_v ≤ 1` such
  that `ψ(x) = 1` for every adele `x` with `x.1 = 0`, `x_v ∈ 𝒪_v` for every finite `v`, and
  `|x_v|_v < |a_v|_v` for `v ∈ T_ψ`.
- **`mul_invariant_of_components`**: let `φ : GL_n(𝔸) → ℂ` be right invariant under
  `AdelicGL.ofFinite j` for `j` in an open subgroup `J` of `GL_n(𝔸_f)`, and under `GL_n(𝒪_v)`
  placed at `v` for every finite `v ∉ S₁`. Then `φ(g a) = φ(g)` for every adelic matrix `a`
  with archimedean component `1`, components `a_v ∈ GL_n(𝒪_v)` at every finite place, and
  `localInclusion v a_v ∈ J` for `v ∈ S₁`.
- `exists_ball_openCellUnipotent_mem J v`: there is `a ≠ 0`, `|a|_v ≤ 1`, such that
  `localInclusion v (u'(y)) ∈ J` (with `u'(y)` reindexed by `blockEquiv r t`) for every local
  `y` with entries of valuation `< |a|_v`.
- `infinite_openCellUnipotent`, `comp_openCellUnipotent_mem`,
  `openCellUnipotent_mem_standardCompact`: for `Z` as above, `u'(Z)` has archimedean
  component `1`, integral finite components, and lies in `standardCompact F (r+t+2)`.
- **`openCellIntegrand_add_of_invariant`**: if `φ_s = φ · H^s` (`Oneplace.twisted`)
  satisfies `φ_s(g u'(Z)) = φ_s(g)` for all `g` and `ψ(Z_(t,0)) = 1`, then
  `openCellIntegrand ψ φ s (Y + Z) = openCellIntegrand ψ φ s Y`.
- **`twisted_mul_openCellUnipotent`**: `φ_s(g u'(Z)) = φ_s(g)` when `φ` is right invariant
  under `J` and spherical outside `S₁` (`IsSphericalOutside F r t S₁ φ`) and
  `localInclusion v (u'(Z)_v) ∈ J` for `v ∈ S₁`.

## Proofs

`exists_finiteBox_eq_one`. The set `O` of finite adeles `y` with `‖ψ(0, y) − 1‖ < 1/2` is a
neighbourhood of `0`. Its preimage under the continuous structure map
`∏_v 𝒪_v → 𝔸_f` (`RestrictedProduct.structureMap`) is a neighbourhood of `0` in the
product topology, so it contains a box `{y | y_v ∈ u_v for v ∈ T_ψ}` with `u_v` neighbourhoods
of `0` in `𝒪_v`; shrink each `u_v` to a ball `|y_v| < |a_v|` (`exists_ball_subset`). The
set `H` of finite adeles integral everywhere with `|y_v| < |a_v|` on `T_ψ` is an additive
subgroup contained in `O`. For `x` as in the statement, `ψ(x)^n = ψ(0, n x_f)` stays within
`1/2` of `1` for every `n`, so `ψ(x) = 1` by
`Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt` (no small subgroups in `ℂˣ`).

`mul_invariant_of_components`. `FiniteAdelicGL.exists_finset_forall_mem` gives a finite set
`T` such that `J` contains every finite adelic matrix that is integral everywhere and `1` at
the places of `T`. Induct over finite sets `T' ⊆ T` of places where the component of `a` may
differ from `1`. If `T'` is empty, `a = ofFinite (finite a)` with `finite a ∈ J`. Otherwise,
for `w ∈ T'`, write `a = adelicAt w a_w · a'`, where `a'` has component `1` at `w` and the
same other components; then `φ(g a) = φ(g · adelicAt w a_w) = φ(g)` by the induction
hypothesis for `a'` and by `J`-invariance (if `w ∈ S₁`) or sphericity (if `w ∉ S₁`).

`openCellIntegrand_add_of_invariant`. By `openCellIntegrand_eq`, `openCellUnipotent_add`
and `leviWhittaker_mul_right_of_invariant`,
`W_M(φ_s)(w u'(Y) u'(Z)) = W_M(φ_s)(w u'(Y))`, and
`ψ(Y_(t,0) + Z_(t,0)) = ψ(Y_(t,0))`.

`twisted_mul_openCellUnipotent`. `H^s` is right invariant under `standardCompact`
(`heightPower_mul_compact`) and `φ` under `u'(Z)` by `mul_invariant_of_components`.

## Provenance

These lemmas are internal to the Library. In the proof of Shahidi (1981), Theorem 5.1,
pp. 351–352 (`shahidi-1981-certain-l`), the corresponding facts are implicit in the
factorization of the Fourier coefficient over the places for a factorizable section: the
finite components of the section are invariant under small open subgroups and spherical
almost everywhere, and the finite components of the additive character are trivial on
small neighbourhoods of `0`.
