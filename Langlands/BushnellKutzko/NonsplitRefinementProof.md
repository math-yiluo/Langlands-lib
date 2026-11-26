# A nonsplit fundamental stratum lies in a simple stratum (BK93 (2.3.4))

Module `Langlands.BushnellKutzko.NonsplitRefinementProof`.
`Langlands.BushnellKutzko.PureApproximation.nonsplitRefinement` proves the unchanged Library
proposition `Langlands.BushnellKutzko.PureApproximation.NonsplitRefinementPremise` (module
`PureStratumApproximationSeed`), with the field and the vector space in independent universes.

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
`bushnell-kutzko-1993-admissible-dual-gln`, (2.3.4), printed p. 58 (PDF p. 70). The source
proof is in §2.5, printed pp. 76–83 (PDF pp. 88–95): (2.5.11) conjugates the stratum into a
"standard form" built from a Jordan canonical form, and (2.5.9) proves (2.3.4) for strata in
standard form. The Lean proof takes a different route, described below; it uses no block
matrices and no Jordan form.

## Statement

For every nonarchimedean local field `F`, finite-dimensional `F`-vector space `V` and stratum
`S = [𝓛, n, r, b]` with `S.IsNonsplit`, there is a stratum `T = [𝓜, n', r', c]` with
`T.IsSimple`, `r' = n' - 1`, `S.coset ⊆ T.coset`, `n e(𝓜) = n' e(𝓛)`, and every lattice of `𝓛`
a lattice of `𝓜`. Here `S.IsNonsplit` (module `FundamentalStratum`) means that `r = n - 1`, the
coset `b + 𝔓^{1-n}(𝓛)` contains no nilpotent element, and for some prime element `ϖ` of `𝔬_F`
the reduction of the characteristic polynomial of `y = ϖ^{n/g} b^{e/g}` is `p^m` for a monic
irreducible `p` over `𝔬_F/𝔭_F` and some `m > 0` (`e = e(𝓛)`, `g = gcd(e, |n|)`).

## Implemented proof

Write `ℓ = -n` and `𝔓^j = 𝓛.endFiltration j`. `exists_shiftParameters_eq_gcd` chooses
`CriticalDerived.ShiftParameters` `(g, h, k, u, v)` with `e = hg`, `ℓ = gk`, `uk + vh = 1` and
`g = gcd(e, |n|)`, so that `y = ϖ^{-k} b^h`.

1. **The element `y`.** The valuation bound of the stratum gives `b ∈ 𝔓^ℓ`
   (`mem_of_le_valuation`), hence `y ∈ 𝔓^{hℓ - ke} = 𝔓^0`.
2. **Integral characteristic polynomial.** `exists_charpoly_eq_map` writes the characteristic
   polynomial of `y ∈ 𝔄(𝓛)` as the image of the characteristic polynomial `Φ` of an integral
   matrix, the matrix of `y` in a basis of `L_0` extended to `V`
   (`Module.Basis.extendOfIsLattice`). By `reduceIntegralPolynomial_map` the Library's reduction
   is the coefficientwise reduction of `Φ`. Let `P ∈ 𝔬_F[X]` be a monic lift of `p`. Then
   `P^m - Φ` has coefficients in `𝔭_F`, and Cayley–Hamilton gives `P(y)^m ∈ 𝔓^1`
   (`aeval_pow_mem_one`).
3. **`p ≠ X`.** Otherwise `y^m ∈ 𝔓^1`, so `b^{hm} = ϖ^{km} y^m ∈ 𝔓^{hm ℓ + 1}`, and
   `LatticeChain.exists_isNilpotent_add_of_pow_mem_endFiltration` (module
   `FundamentalStratumPowerCondition`) gives a nilpotent element of `b + 𝔓^{ℓ+1} = S.coset`,
   contradicting fundamentality. Hence `p(0) ≠ 0`, and `P(0)` is a unit of `𝔬_F`.
4. **Units.** `exists_unit_of_aeval_pow_mem`: write `P^m = c₀ + X R` with `c₀ ∈ 𝔬_F^×`. Then
   `y · (-c₀⁻¹ R(y)) = 1 - c₀⁻¹ P(y)^m` lies in `1 + 𝔓^1`, which consists of units of `𝔄(𝓛)`
   (`LatticeChain.exists_mem_unitFiltration`). So `y` is a unit of `𝔄(𝓛)`, `b^h = ϖ^k y` is a
   unit, `b` is a unit, and `shifts_of_pow` shows that `b` shifts `𝓛` by `ℓ`, that is,
   `b L_i = L_{i+ℓ}`. In the unit group, `y = b^h ϖ^{-k}` is `ShiftParameters.residual`.
5. **The finer chain.** `z = P(y)` lies in `𝔄(𝓛)`, satisfies `z^m ∈ 𝔓^1`, and commutes with `b`
   and `y`. `NonsplitRefinement.exists_refinement` (module `NonsplitRefinementChain`) gives the
   chain `𝓜` of the lattices `z^t L_i + L_{i+1}` and `ℓ'` such that `b` shifts `𝓜` by `ℓ'`,
   every `L_i` lies in `𝓜`, `𝔓^{ℓ+1}(𝓛) ⊆ 𝔓^{ℓ'+1}(𝓜)`, `z ∈ 𝔓^1(𝓜)`, and `y` is a unit of
   `𝔄(𝓜)`. Comparing the shift `0` of `y` with the shift `hℓ' - k e(𝓜)` of `b^h ϖ^{-k}` gives
   `hℓ' = k e(𝓜)`. As `h` and `k` are coprime, `e(𝓜) = h g'` and `ℓ' = g' k` for some
   `g' > 0`, and `(g', h, k, u, v)` are shift parameters for `(e(𝓜), ℓ')` with the same
   residual `y`.
6. **The simple element.** `CriticalDerived.exists_simple_cyclic_lift` (module
   `CriticalDerivedSimpleLift`) applies on `𝓜` to `b`, `ℓ'` and `P`: `P` is monic with unit
   constant coefficient, its reduction to the residue field `IsLocalRing.ResidueField 𝔬_F` is
   the image of `p` under `𝔬_F/𝔭_F ≃ ResidueField 𝔬_F` and so irreducible, and `P(y) ∈ 𝔓^1(𝓜)`.
   It gives `c ∈ 𝔓^{ℓ'}(𝓜)` with `c - b ∈ 𝔓^{ℓ'+1}(𝓜)`, such that `F[c]` is a field whose units
   normalize `𝓜` and `k₀(c, 𝓜) ≤ ℓ'`.
7. **The simple stratum.** Take `T = [𝓜, -ℓ', -ℓ' - 1, c]`. Since `b ∉ 𝔓^{ℓ'+1}(𝓜)`, also
   `c ∉ 𝔓^{ℓ'+1}(𝓜)`, so `v_𝓜(c) = ℓ'` and `T` is pure; `k₀(c, 𝓜) ≤ ℓ' < -r'` makes it simple.
   For `x ∈ S.coset`, `x - c = (x - b) - (c - b) ∈ 𝔓^{ℓ'+1}(𝓜) = 𝔓^{-r'}(𝓜)`. Finally
   `n e(𝓜) = -gk e(𝓜) = -g h ℓ' = n' e(𝓛)`.

The proof uses neither `CriticalDerivedStratumStatement` ((2.4.1)(iii)) nor the aggregate
`StratumApproximationStatement`. From the critical-derived development it uses the cyclic-lift
theorem `exists_simple_cyclic_lift` to construct the simple representative `c`. It also uses that
development's supporting material on shifting units and normalization:

- `Shifts` with `Shifts.mul` and `Shifts.zpow`, `Shifts.stabilizerValuation_eq` (module
  `CriticalDerivedSymbols`);
- `uniformizerUnit_shifts` (module `CriticalDerivedCyclicRows`) and `scalarEndUnit_commutes`
  (module `CriticalDerivedCyclicAction`);
- the Bézout normalization `ShiftParameters`, with `ShiftParameters.residual` and
  `ShiftParameters.residual_degree` (module `CriticalDerivedNormalization`).

## Auxiliary declarations (namespace `Langlands.BushnellKutzko.NonsplitRefinement`)

- `integer_smul_mem`, `jacobson_smul_mem`, `zpow_smul_mem`, `pow_mem_endFiltration`: scalars in
  `𝔬_F` preserve `𝔓^j`, scalars in `𝔭_F` raise the degree by one, `ϖ^t` raises it by `e t`, and
  `x ∈ 𝔓^j ⇒ x^k ∈ 𝔓^{kj}`.
- `aeval_map_mem_order`, `aeval_map_mem_one`, `commute_aeval`: integral polynomials in
  `y ∈ 𝔄(𝓛)` lie in `𝔄(𝓛)`, and in `𝔓^1` when all coefficients lie in `𝔭_F`; an element
  commuting with `y` commutes with every polynomial in `y`.
- `coe_scalarEndUnit_zpow`: integer powers of a scalar endomorphism unit.
