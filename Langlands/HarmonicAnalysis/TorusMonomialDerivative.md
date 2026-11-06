# Angular derivatives along an integer torus monomial

Lean module: `Langlands.HarmonicAnalysis.TorusMonomialDerivative`, namespace
`Langlands.HarmonicAnalysis.TorusFourier`. It imports:

- `Langlands.HarmonicAnalysis.TorusFourierDecay` (Worker 249): the angular derivative
  `torusPartialDeriv`, `torusPartialDeriv_finiteTorusExp`,
  `isSmoothFiniteTorusFunction_torusPartialDeriv` and the bound `exists_norm_le_of_isSmooth`;
  through its imports `IsSmoothFiniteTorusFunction`, `finiteTorusExp`, `finiteTorusExp_add` and
  `isOpenQuotientMap_finiteTorusExp` (`Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions`);
- `Langlands.Representation.Plancherel.RationalOrbitBasisInvariance`: the integer monomial map
  `finiteTorusMonomial a z = (∏ₖ z_k^{a j k})_j`, its real lift `finiteTorusMonomialLift`,
  `finiteTorusExp_monomialLift` and `IsSmoothFiniteTorusFunction.comp_monomial`.

The names `IsSmoothFiniteTorusFunction`, `finiteTorusMonomial` and the other `Plancherel`
declarations are read in the namespace `Langlands.Plancherel` (opened).

## Provenance

Derived; no statement of the paper. J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082 (literature id `waldspurger-2003-plancherel`), proof of Prop. VI.3.1,
printed p. 303 (PDF p. 69), defines `ϕ_g(χ) = ∫_{Im X(G)} ϕ(λχ) λ(g) dλ` and bounds it by
estimate (4), `|∫_{Im X(G)} ϕ'(λ) λ(g) dλ| ≤ (1 + (H_G(g)))^{-r} ν_G(D, ϕ')`, applied to
`ϕ'(λ) = ϕ(λχ)`. The seminorm `ν_G(D, ϕ')` involves derivatives of `λ ↦ ϕ(λχ)` along
`Im X(G)`, which have to be bounded uniformly in `χ ∈ Im X(M)` by derivatives of `ϕ`. In
torus coordinates the restriction `Im X(G) → Im X(M)` is an integer monomial map
`finiteTorusMonomial a` (`a` an integer matrix), and this module supplies those uniform bounds
by the chain rule. The paper takes this step for granted.

## Scope and hypotheses

`J`, `K` are finite types (`[Fintype J]`, `[Fintype K]`); from `monomialPartialDeriv` on also
`[DecidableEq J]`, and the chain-rule statements and the bound take `[DecidableEq K]`. The
linter `omit`s unused instances: `finiteTorusMonomial_mul`, `continuous_finiteTorusMonomial`
need only `[Fintype K]`; `finiteTorusMonomialLift_add_single` needs only `[Fintype K]` and
`[DecidableEq K]`; `isSmoothFiniteTorusFunction_monomialPartialDeriv` and its iterate need
`[Fintype J]` and `[DecidableEq J]`. `a : J → K → ℤ` is an arbitrary integer matrix and
`Φ : (J → Circle) → ℂ`; the results about `Φ` assume `hΦ : IsSmoothFiniteTorusFunction Φ`.

## Definitions

- `monomialPartialDeriv a k Φ : (J → Circle) → ℂ`, `y ↦ ∑ⱼ a j k · torusPartialDeriv j Φ y`:
  the angular derivative in the direction of the `k`-th coordinate of `K → Circle` pushed
  forward by the monomial map.

## Results

- `finiteTorusMonomial_mul`: `finiteTorusMonomial a (z w) = finiteTorusMonomial a z ·
  finiteTorusMonomial a w`.
- `continuous_finiteTorusMonomial`: the monomial map is continuous.
- `isSmoothFiniteTorusFunction_comp_monomial_mul`: for smooth `Φ` and every `y : J → Circle`,
  `z ↦ Φ(finiteTorusMonomial a z · y)` is smooth on `K → Circle`.
- `isSmoothFiniteTorusFunction_monomialPartialDeriv`,
  `isSmoothFiniteTorusFunction_iterate_monomialPartialDeriv`: `monomialPartialDeriv a k Φ` and
  its iterates are smooth for smooth `Φ`.
- `finiteTorusMonomialLift_add_single`: `finiteTorusMonomialLift a (x + θ e_k) =
  finiteTorusMonomialLift a x + θ (a j k)_j`.
- `torusPartialDeriv_comp_monomial_mul` (chain rule): the `k`-th angular derivative of
  `z ↦ Φ(finiteTorusMonomial a z · y)` at `z` is
  `monomialPartialDeriv a k Φ (finiteTorusMonomial a z · y)`.
- `iterate_torusPartialDeriv_comp_monomial_mul`: the `n`-th iterate of that derivative is
  `z ↦ ((monomialPartialDeriv a k)^[n] Φ)(finiteTorusMonomial a z · y)`.
- `exists_bound_comp_monomial_mul`: for smooth `Φ` and `n : ℕ` there is `M ≥ 0` with
  `‖Φ(finiteTorusMonomial a z · y)‖ ≤ M` and
  `‖(torusPartialDeriv k)^[n] (z ↦ Φ(finiteTorusMonomial a z · y)) z‖ ≤ M` for all `y`, `k`,
  `z`.

## Proof notes

1. Multiplicativity: `mul_zpow` and `Finset.prod_mul_distrib` coordinatewise. Continuity:
   `continuous_finsetProd` of `zpow` of coordinate projections.
2. Translation: write `y = finiteTorusExp b`; `Φ(w · finiteTorusExp b) ∘ finiteTorusExp` is
   `(Φ ∘ finiteTorusExp) ∘ (· + b)`, smooth; then `IsSmoothFiniteTorusFunction.comp_monomial`.
3. Smoothness of `monomialPartialDeriv`: a finite sum of constants times smooth derivatives
   (`ContDiff.sum`); iterates by induction.
4. Chain rule: with `z = finiteTorusExp x` and `y = finiteTorusExp b`, the curve
   `θ ↦ finiteTorusMonomial a (z · finiteTorusExp (θ e_k)) · y` is
   `finiteTorusExp (u + θ v)` with `u = finiteTorusMonomialLift a x + b` and `v = (a j k)_j`
   (`finiteTorusMonomialLift_add_single`, `finiteTorusExp_monomialLift`). Its derivative at
   `0` is `fderiv (Φ ∘ finiteTorusExp) u v` (`HasFDerivAt.comp_hasDerivAt`); expanding
   `v = ∑ⱼ a j k e_j` and using `torusPartialDeriv_finiteTorusExp` gives the sum.
5. Iterates: induction on `n` with step 4 applied to the smooth iterate.
6. Bound: `exists_norm_le_of_isSmooth` for `Φ` and for each iterate
   `(monomialPartialDeriv a k)^[n] Φ`; the constant is `|M₀| + ∑ₖ |M k|`.

## Relation to the Library

- `TorusFourierAveraging.norm_integral_mul_le_rpow` (Worker 249) takes a continuous
  `ι : (J → Circle) → T` and assumes bounds on the derivatives of `z ↦ φ(ι(z) χ)`, uniform in
  `χ`. With `T = J → Circle` (the torus `Im X(M)` in coordinates) and
  `ι = finiteTorusMonomial a`, `exists_bound_comp_monomial_mul` and
  `isSmoothFiniteTorusFunction_comp_monomial_mul` supply these hypotheses; this is how
  `OrbitWavePacketDecay` uses them.
- `IsSmoothFiniteTorusFunction.comp_monomial` (Library) is the case `y = 1` of
  `isSmoothFiniteTorusFunction_comp_monomial_mul` and is used in its proof.
