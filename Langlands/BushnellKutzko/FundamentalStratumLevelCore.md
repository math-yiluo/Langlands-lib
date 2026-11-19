# A contained fundamental stratum computes the normalized level

`Langlands.BushnellKutzko.FundamentalStratumLevelCore` proves
`Langlands.BushnellKutzko.fundamentalStratumLevel_of_containsStratum`. Let `K`
be a p-adic field, `n ≥ 1`, `ψ` a level-one additive character and `a` an
irreducible admissible class of `GL_n(K)`. Suppose `𝓛` is an `𝔬_K`-lattice chain
in `K^n`, `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)` and `ContainsStratum K n ψ a 𝓛 m b`. If
`∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ¬ IsNilpotent (b + y)`, then
`IsNormalizedLevel K n a ((m : ℚ) / 𝓛.period)`.

The theorem has the binders and conclusion of the body of
`Langlands.BushnellKutzko.FundamentalStratumLevelStatement`, with independent
universes `uK` for `K` and `uV` for the representation carrier. Its explicitly
named local instances `fslCoreTopologicalSpace`, `fslCoreValuativeRel`,
`fslCoreLocalField` and `fslCoreTopologicalSpaceGL` use the same canonical
data as the statement. `FundamentalStratumLevelProof` applies the theorem to
that proposition.

## Sources

Bushnell (1987), Theorem 1, printed p. 192, gives the level reduction when
there is a nilpotent representative. Remark (2.9), printed p. 195, gives the
related criterion for a coset to have such a representative. The minimizing
order appears in (3.3) and Theorem 2′, printed pp. 196–197
(`bushnell-1987-hereditary-orders-gauss-sums`). Bushnell–Kutzko (1993),
Introduction, printed p. 8, gives the common normalized level of contained
fundamental strata. Its §2.3, printed p. 57, defines fundamentality and gives
the smaller-level result (2.3.1). The trace character and its triviality
come from (1.1.4)–(1.1.6), printed p. 22
(`bushnell-kutzko-1993-admissible-dual-gln`).

The implemented minimality argument uses the intertwining step of the operator
note's Lemma 4.11(i), printed pp. 15–16. Triviality holds on the intersection
with the transported step `𝔓^{m''+1}` because the fixed subgroup is
`U^{m''+1}`. The coordinate weights in `LatticeChain.exists_isNilpotent_add`
then give the nilpotent representative (`operator-numerical-llc-route-2026-11-16`).

## Imports

- `Langlands.BushnellKutzko.FundamentalStratumDual` supplies the nilpotent
  representative and imports the shared `FiltrationCoordinates` and its
  `SplittingBasis` dependency.
- `Langlands.BushnellKutzko.IntertwiningAveraging` supplies finite averaging and
  the compact-open index lemma.
- `Langlands.BushnellKutzko.NormalizedLevel` supplies `IsLevelOne`,
  `ContainsStratum`, `normalizedLevelValues`, `IsNormalizedLevel` and `unitSubgroup`.
- `Langlands.Representation.Conductor.PrincipalCongruenceBasisProof` supplies
  `Conductor.mem_principalCongruenceSubgroup_iff`.

## Attainment and minimality

Write `n = n' + 1` and choose a uniformizer `ϖ`. From `ContainsStratum`, choose
a representative `A` of `a` with a nonzero vector `v` satisfying
`A(h) v = χ(h) v` on `U^m = unitSubgroup K 𝓛 m`. The code defines `χ(h)` by
`elementCharacter (traceCharacter ψ) b (toLin h)`, which evaluates to
`ψ(tr(b (toLin h - 1)))`.

1. If `h ∈ U^{m+1}`, multiplying `b ∈ 𝔓^{-m}` by `toLin h - 1 ∈ 𝔓^{m+1}`
   gives an element of `𝔓^1`, by `LatticeChain.mul_mem_endFiltration`.
   `LatticeChain.addChar_trace_eq_one` gives `χ(h) = 1` since `ψ` is trivial
   on `𝔭_K`. As `U^{m+1} ≤ U^m`, the same `v` is fixed by `U^{m+1}` and
   `(𝓛, m)` witnesses `m/e ∈ normalizedLevelValues`, where `e = 𝓛.period`.
2. Let `(𝓛'', m'')` witness a smaller attained value `m''/e''`, with
   `e'' = 𝓛''.period`, and let `w ≠ 0` be fixed by
   `J = unitSubgroup K 𝓛'' (m'' + 1)`. The positive periods give
   `m''·e < m·e''` in `ℤ`. The argument includes `m'' = 0`.
3. Apply `exists_forall_conj_mem_eq_one` with `H = U^m` and `N = U^{m+1}`.
   The relative indices are finite by compactness of `H` and openness of
   `N` and of the conjugates of `J`. The result is a matrix `g` such that
   `χ(h) = 1` for `h ∈ H` with `g⁻¹ h g ∈ J`.
4. Put `P = toLin g` and `𝓛''' = 𝓛''.mapUnit P`. Its period is `e''`.
   For `x ∈ 𝔓^m(𝓛) ∩ 𝔓^{m''+1}(𝓛''')`, use
   `LatticeChain.exists_mem_unitFiltration` to obtain a unit endomorphism
   `u = 1 + x` in the first chain's step `m`. Then `h = toLin.symm u` belongs
   to `H`. Transport gives `P⁻¹ x P ∈ 𝔓^{m''+1}(𝓛'')`, so the unit from
   `1 + P⁻¹ x P` corresponds to `g⁻¹ h g ∈ J`. Thus `χ(h) = 1`, which
   reduces to `ψ(tr(b x)) = 1` using `u = 1 + x`.
5. The other half of `IsLevelOne` supplies `s ∈ 𝔬_K` with `ψ(s) ≠ 1`.
   Apply `LatticeChain.exists_isNilpotent_add` to `𝓛` and `𝓛'''` with
   this `s`, the strict period-weighted inequality, and the trace identity.
   The resulting nilpotent element of `b + 𝔓^{1-m}(𝓛)` contradicts the
   fundamentality hypothesis. The attained value `m/e` is therefore minimal.

## Supporting lemmas

- `addChar_sum_eq_one` handles a finite sum whose terms all have character
  value one. `exists_mem_maximalIdeal_of_one_le_ordOf` puts each nonzero field
  element of valuation at least one in `𝔭_F`. In
  `LatticeChain.addChar_trace_eq_one`, `LatticeChain.exists_basis_splits` gives a
  basis for one chain. For `x ∈ 𝔓^1`, each nonzero diagonal entry satisfies
  `e·ord(x_{kk}) ≥ 1`, and thus lies in `𝔭_F`. The trace is their sum with
  the zero entries included, and its character value is one.
- `LatticeChain.exists_endFiltration_le` gives an `N` such that
  `𝔓^N(𝓛') ⊆ 𝔓^j(𝓛)` for two chains in `F^ι` and `j ∈ ℤ`. In a
  common splitting basis it bounds the sum of the absolute chain indices of
  each basis vector by `C`. If `e'` is the period of `𝓛'`, then
  `N = e'(|j| + 2C) + 2C` makes the entry inequalities for `𝔓^N(𝓛')`
  imply those for `𝔓^j(𝓛)`.
- `LatticeChain.sub_one_mem_standard_endFiltration` compares a principal
  congruence subgroup with the standard chain. The entrywise congruences
  defining `Conductor.principalLevelSubgroup F n N` put `toLin h - 1`
  in `𝔓^N` for the standard chain.
- `LatticeChain.mapUnit` applies `LatticeChain.linearEquivMap` to the linear
  equivalence of a unit endomorphism `P`. `mem_mapUnit_lattice` uses
  `mem_linearEquivMap` to express membership in `P L_i` as membership of
  `P⁻¹ v` in `L_i`. `period_mapUnit` uses `period_unique` and commutation of
  scalar multiplication with the submodule image. The membership formula
  gives `conj_mem_endFiltration_of_mem_mapUnit` by applying `x` to `P v`.
- `isOpen_unitSubgroup` uses the comparison with the standard chain to find
  an open principal congruence subgroup in `U^j`. Each element of that
  principal subgroup and its inverse lie in the lattice-chain order, and
  subtracting one from the element gives membership in `𝔓^j`. `Subgroup.isOpen_mono`
  yields openness.
- `isCompact_unitSubgroup` takes a field basis obtained from a basis of `L_0`
  using `Module.Basis.extendOfIsLattice`. For `h ∈ U^0`, both `h` and `h⁻¹`
  preserve `L_0`. In this basis both matrices have integral entries by
  `repr_extendOfIsLattice_mem`, placing the conjugated subgroup in the compact
  `Conductor.principalLevelOpenSubgroup K.Carrier n 0`. Thus `U^j ⊆ U^0`
  is a closed subset of a conjugate of this compact group.
