# The decomposition of `∫_G f_1(a g a^{-1}) f_2(g) dg` in the proof of Proposition VIII.3.1

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalSplit`, namespace
`Langlands.HarishChandraSchwartz`. It imports `ParabolicHaar` (submitted with this module:
`leviUnipotentCoord`, `leviUnipotentMeasure`, `leviUnipotentMeasure_isHaarMeasure`,
`openCellCoord`, `eq_smul_map_openCellCoord`) and the published `CuspidalDecay`
(`cuspidalFactor`, `unipotentFactor`, and through it `IsConjModulus.integral_comp` of
`ConstantTermInd`); `OpenCellIntegration` supplies `openCellMap`, `openCellConstant` and
`lintegral_eq_openCellConstant_inv_mul`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Proof of Proposition VIII.3.1, printed pp. 323–324 (PDF
pp. 89–90): `f_1` is left invariant by `Γ ⊆ U` and `f_2` right invariant by `Γ̄ ⊆ Ū`;
`S(a) = G - a^{-1} Γ a M Γ̄`;

`J(a) = ∫_{a^{-1} Γ a M Γ̄} f_1(a g a^{-1}) f_2(g) dg
= γ(G|M)^{-1} ∫_{a^{-1}Γa × M × Γ̄} f_1(a u m ū a^{-1}) f_2(u m ū) δ_P(m)^{-1} dū dm du`,

`φ_1(a, m) = δ_P(m)^{-1/2} ∫_{Γ̄} f_1(m a ū a^{-1}) dū`,
`φ_2(a, m) = δ_P(m)^{-1/2} ∫_{a^{-1}Γa} f_2(u m) du`, and
"by the choices of `Γ` and `Γ̄`", `J(a) = γ(G|M)^{-1} ∫_M φ_1(a, a m a^{-1}) φ_2(a, m) dm`.
The integral over `G` is the integral over `S(a)` plus `J(a)`.

## Scope: abstract data and explicit hypotheses

The setting is that of `ParabolicHaar`: `G` a topological group with its Borel σ-algebra;
subgroups `M`, `U`, `P`, `V` (for Waldspurger `V = Ū`) with `M` normalizing `U` (`hMU`) and `V`
(`hMV`), `U` second countable, `P` and `V` locally compact and second countable, and
`m u ∈ P` (`hP`); `μ` a Haar measure on `G` that is also right invariant; Haar measures `μ_M`
(s-finite), `μ_U` (s-finite) and `μ_V`. Hypotheses of `integral_conj_mul_eq_split`, none of them
proved here for Waldspurger's data:

- the open-cell hypotheses `hhomeo`, `hι`, `hnull` and `K` measurable with `0 < μ(K) < ∞`, as in
  `lintegral_eq_openCell_levi_unipotent`;
- `IsConjModulus hMU μU δ` (`hν`; `δ = δ_P`), `μ_V` inversion invariant, and a character `δ̄`
  with `δ̄ = δ^{-1}` on `M` (`hδbar`; `δ̄ = δ_{P̄}`, the modulus used in `cuspidalFactor`);
- `Γ ⊆ G` and a subgroup `Γ̄` of `V`, with `f_1(γ x) = f_1(x)` for `γ ∈ Γ` (`hf₁`) and
  `f_2(x γ̄) = f_2(x)` for `γ̄ ∈ Γ̄` (`hf₂`);
- for the given `a ∈ M`, a measurable set `Ω ⊆ G` (`hΩ`) with
  `m u v^{-1} ∈ Ω ↔ a (m u m^{-1}) a^{-1} ∈ Γ ∧ v ∈ Γ̄` for `m ∈ M`, `u ∈ U`, `v ∈ V` (`hΩmem`; for
  Waldspurger `Ω = a^{-1} Γ a M Γ̄`, and this is the uniqueness of the open-cell coordinates);
- the set `A = {u ∈ U | a u a^{-1} ∈ Γ}` (Waldspurger's `a^{-1} Γ a`) is measurable (`hA`);
- `g ↦ f_1(a g a^{-1}) f_2(g)` is `μ`-integrable (`hint`).

## Results

- `integral_eq_smul_integral_openCellCoord` (under the open-cell hypotheses): for `F`
  integrable, `F ∘ openCellCoord` is integrable for `(μ_M × μ_U) × μ_V` and
  `∫_G F dμ = c ∫ F(m u v^{-1})` with `c = μ(K) γ^{-1}` (the Bochner form of
  `eq_smul_map_openCellCoord`).
- `sqrt_mul_inv_sqrt_eq` (any group `M`): if `δ̄ = δ^{-1}`, then
  `δ̄(a m a^{-1})^{1/2} δ(m)^{-1/2} = δ(m)^{-1}`.
- `integral_conj_mul_eq_split`:
  `∫_G f_1(a g a^{-1}) f_2(g) dμ = ∫_{Ωᶜ} f_1(a g a^{-1}) f_2(g) dμ +
  c ∫_M cuspidalFactor(a, a m a^{-1}) unipotentFactor(m) dμ_M`, where `cuspidalFactor` is taken
  for `(V, μ_V, δ̄, Γ̄)`, so that it is
  `δ̄(m')^{1/2} ∫_{Γ̄} f_1(m' a v a^{-1}) dμ_V(v)`, and `unipotentFactor` for `(U, μ_U, δ, A)`, so
  that it is `δ(m)^{-1/2} ∫_A f_2(u m) dμ_U(u)`. This is exactly the hypothesis `hsplit` of
  `conjugationIntegralBound_of_split` (with `S(a) = Ωᶜ`, the constant `c` in place of
  `γ(G|M)^{-1}`, and the factors in the form used by `lintegral_cuspidal_le`).

- `conjugationIntegralBound_of_openCell` (Proposition VIII.3.1 from the open-cell data):
  under the hypotheses of `integral_conj_mul_eq_split` for every `a` in a set `T ⊆ M` (with a
  family `Ω(a)`: `hΩ`, `hΩmem`, `hA`, `hint` quantified over `a ∈ T`), and the two estimates
  `h3` (for every `r` a `c` with `∫⁻_{Ω(a)ᶜ} |f_1(a g a^{-1})| |f_2(g)| dμ ≤ c e(a)^2 (1 + σ(a))^{-r}`
  on `T`; inequality (3) of the proof, as proved by `ConvolutionWeights.lintegral_conj_mul_le`)
  and `hJ` (the same bound for `∫⁻_M |φ_1(a, a m a^{-1})| |φ_2(a, m)| dμ_M`, the conclusion of
  `lintegral_cuspidal_le`), `ConjugationIntegralBound μ T f_1 f_2 e σ` holds. It is
  `conjugationIntegralBound_of_split` with `hsplit` supplied by `integral_conj_mul_eq_split`.

## Proof notes

The integral over `G` splits over `Ω` and its complement (`integral_add_compl`). On `Ω` the
integral of the indicator is computed with the open-cell formula in the coordinates
`m u v^{-1}` and Fubini. In these coordinates `m u v^{-1} = (m u m^{-1}) m v^{-1}`; on `Ω`,
`a (m u m^{-1}) a^{-1} ∈ Γ` and `v^{-1} ∈ Γ̄`, so the invariances give
`f_1(a m u v^{-1} a^{-1}) = f_1(a m v^{-1} a^{-1})` and `f_2(m u v^{-1}) = f_2((m u m^{-1}) m)`.
The integrand therefore factors as the product of a function of `(m, v)` and a function of
`(m, m u m^{-1})`. The `U`-integral is changed by `u ↦ m u m^{-1}` (`IsConjModulus.integral_comp`,
factor `δ(m)^{-1}`), the `V`-integral by `v ↦ v^{-1}` (inversion invariance; `Γ̄` is a
subgroup), and `a m v a^{-1} = (a m a^{-1})(a v a^{-1})`. The factor `δ(m)^{-1}` is split as
`δ̄(a m a^{-1})^{1/2} δ(m)^{-1/2}` (`sqrt_mul_inv_sqrt_eq`).

## Open obligations

For Waldspurger's data: the open-cell hypotheses (see `ParabolicHaar` and
`OpenCellIntegration`), the modulus relations for `δ_P` and `δ_{P̄} = δ_P^{-1}`, the
inversion invariance of `dū`, the description `hΩmem` of `a^{-1} Γ a M Γ̄` in coordinates, the
invariance of `f_1`, `f_2` under the chosen compact open subgroups, and the integrability of
`g ↦ f_1(a g a^{-1}) f_2(g)` for `f_1, f_2 ∈ C(G)` are not proved here.
