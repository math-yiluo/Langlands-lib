# Proof of the spherical cyclicity in the closed Langlands chamber

Lean module: `Langlands.Representation.Archimedean.RealSphericalCyclicProof`, namespace
`Langlands.Archimedean.RealSphericalCyclicProof`. The main theorem is

`theorem realSphericalCyclic : RealSphericalCyclicStatement`,

which proves the Library statement `Langlands.Archimedean.RealSphericalCyclicStatement`
(module `RealSphericalCyclic`). The statement and its provenance are described in
`RealSphericalCyclic.md`. Briefly: for a list `ds` of `n` parity-zero real characters whose
exponents have weakly decreasing real parts, every Lie-stable subspace `W` of the `O(n)`-finite
vectors of the standard module that contains a nonzero `O(n)`-fixed vector `T` is everything.

The proof uses the helper modules `RealSphericalKrylov`, `RealSphericalStep`,
`RealSphericalReach`, `RealSphericalChart`, `RealSphericalLimit` and
`RealSphericalInduction`. It uses no Langlands quotient theorem or classification for lists
with ties.

## Lists of characters

Write `cs = ds.map RealBlock.character`.

- `RealPrincipalSeriesDuality.realInducedBlockAt_map_character`: `cs` has no induced (discrete-series) blocks.
- `realStandardModule_map_character`: hence `realStandardModule n cs` is the principal series
  `principalSeries ℝ n χ` of the position characters `χ = realPositionCharacter cs`.
- `realPositionCharacter_map_one`, `realPositionCharacter_map_neg_one`: `χ_l(1) = 1`, and
  `χ_l(−1) = 1` when all parities are `0` (`RealCharacterData.character_eq`).
- `isSignedPower_map`: `χ` is a signed power with exponents `e = realPositionExponent cs`
  (`realPositionCharacter_eq_signUnit_mul`).
- `isWeaklyDominant_map`: `IsRealLanglandsOrdered cs` implies
  `IsWeaklyDominant e (ds.length − 1)`. The pairwise ordering is applied to consecutive
  entries.
- `unitary_toUnits_mk`: the unitary-group element of `k ∈ O(n)` maps back to `k`.

## The proof of `realSphericalCyclic`

1. **Largest `O(n)`-stable subspace.** Put `W' = ⨅_{k ∈ O(n)} k⁻¹ W`, so that `w ∈ W'` iff
   `k · w ∈ W` for all `k`. `W'` is `O(n)`-stable, and it is stable under `R(1 ⊗ X)` for real
   `X`: by the Library's `rightTranslation_rightDerivative`,
   `k · R(X) w = R(k X k⁻¹)(k · w)`, and `W` is Lie-stable. `T ∈ W'` because `T` is fixed and
   `T ∈ W`.
2. **Function spaces.** `V` is the image of `W'` in functions on `GL_n(ℝ)`. It lies in the
   `O(n)`-finite principal series of `χ`, and it is stable under right translation by `O(n)`
   and under all right derivatives.
3. **The fixed vector.** `T(k) = T(1)` for `k ∈ O(n)`, and `T(1) ≠ 0`: otherwise `T`
   vanishes on `O(n)`, hence everywhere by the Iwasawa decomposition, contradicting `T ≠ 0`.
4. **The annihilator.** `A = JacquetKernel.annihilator χ V` is the set of `O(n)`-finite `u`
   in the principal series of `dualChar χ` with `∫_{O(n)} u v = 0` for `v ∈ V`. It is
   `O(n)`-stable and stable under right derivatives (`annihilator_rightTranslation`,
   `annihilator_rightDerivative`). For `u ∈ A`, `0 = ∫ u T = T(1) ∫_{O(n)} u`, so
   `∫_{O(n)} u = 0`.
5. **`A = 0`.** By `RealSphericalInduction.eq_bot`, with trivial signs and weakly dominant
   exponents.
6. **`W = ⊤`.** If some `w` were not in `V`, the Library's `JacquetKernel.annihilator_ne_bot`
   would give `A ≠ 0`. So every `w` lies in `W'`, and taking `k = 1` in the definition of `W'`
   gives `w ∈ W`.

## Provenance

The theorem is Kostant's cyclicity of the spherical vector for `GL_n(ℝ)`, as quoted in
N. Wallach, *Cyclic vectors and irreducibility for principal series representations*,
Trans. Amer. Math. Soc. 158 (1971), 107–113, Theorem 3.1 (see `RealSphericalCyclic.md`). The
formal proof does not follow Kostant or Wallach. It reduces cyclicity to the vanishing of the
annihilator, step 6, and proves that vanishing by an induction along `P_{n−1,1}` modelled on the
Library's strict Langlands lemma (`JacquetDual`, `JacquetLimit`). The new ingredient is a
regularized spherical vector `H` in the Lie span of `T`. It is reached by a Krylov argument
(`RealSphericalKrylov`, `RealSphericalStep`, `RealSphericalReach`), and its partial Jacquet
integrals converge with nonzero value in the closed chamber (`RealSphericalChart`,
`RealSphericalLimit`).
