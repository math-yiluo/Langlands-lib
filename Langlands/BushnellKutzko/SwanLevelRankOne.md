# The Swan conductor and the normalized level in rank one

Lean proof by Worker 408 for Task 7683.

## Setting

`F` is a nonarchimedean local field with ring of integers `𝒪[F]`, maximal ideal `𝔭` and a
uniformizer `ϖ` (`hϖ : Irreducible ϖ`); `ordOf hϖ` is the valuation normalized by
`ordOf ϖ = 1` (module `SplittingBasis`). `LatticeChain.standard hϖ ι` is the Library's standard
lattice chain `L_i = ϖ^i 𝒪[F]^ι`; `𝓛.period` is the period `e(𝓛)`; `𝓛.endFiltration j` is the
filtration `𝔓^j(𝓛)` of `End_F(F^ι)` (Library module `LatticeChain`). For a `p`-adic field `K`
(canonical instances, local instance names `ro*`), `unitSubgroup K 𝓛 m` is the Library's
`U^m(𝔄(𝓛))` in `GL_N(K)`, `Conductor.levelSubgroup K 0 c` is the Library's level subgroup of
`GL_1(K)`, the image of the units of `𝒪_K` congruent to `1` modulo `𝔭^c`, and
`SmoothDualClass.HasFixedVector H a` says that a representative of the class `a` has a nonzero
`H`-fixed vector. `IsNormalizedLevel` and `firstFixedLevel` are as in `SwanLevelHigherRank.md`.

## Declarations

- `toLin'_sub_one_rankOne`: for a `1 × 1` matrix `y`, `toLin'(y - 1)` is the scalar `y₀₀ - 1`
  times the identity.
- `le_ordOf_of_mem_maximalIdeal_pow`: a nonzero element of `𝔭^c` has `ordOf` at least `c`.
- `LatticeChain.standard_period`: the standard lattice chain has period `1`.
- `levelSubgroup_le_unitSubgroup`: for a lattice chain `𝓛` in `K^1` and natural numbers `c`,
  `m` with `m + 1 ≤ e(𝓛) c`, the level subgroup `1 + 𝔭^c` of `GL_1(K)` lies in
  `U^{m+1}(𝔄(𝓛))`.
- `unitSubgroup_standard_le_levelSubgroup`: for `c ≥ 1`, `U^c(𝔄)` of the standard chain in
  `K^1` lies in the level subgroup `1 + 𝔭^c`.
- `hasFixedVector_of_le_rankOne`: a class with a nonzero `H`-fixed vector has a nonzero `H'`-fixed vector
  for every subgroup `H' ≤ H` of `GL_1(K)`.
- `exists_firstFixedLevel_eq_of_isNormalizedLevel_rankOne` (T2 in rank one): let `π` be an
  irreducible supercuspidal class of `GL_1(K)` whose underlying class has normalized level `x`.
  Then the first fixed level of `π` is a natural number `c`, and `c - 1 = x` with truncated
  subtraction.

## Provenance

For a character `χ` of `K^×` of conductor exponent `c ≥ 1`, the normalized level (Bushnell
1987, (3.3), printed p. 196) is `c - 1`; for an unramified character both are `0`. This is the
rank-one convention stated in the context of Task 7683, and the rank-one case of the target T2
with `0 - 1 = 0`; it follows directly from the definitions, as below. The auxiliary declarations are internal steps, not numbered results of the
literature. The proof uses only the two comparisons of subgroups of `K^×` and the definitions;
supercuspidality enters only through the types of `π` and `firstFixedLevel`.

## Proof

`toLin'_sub_one_rankOne` is a computation on `Fin 1`. `le_ordOf_of_mem_maximalIdeal_pow`: write
the element as `z ϖ^c` with `z ∈ 𝒪[F]` nonzero, so `ordOf = ordOf z + c ≥ c`.
`LatticeChain.standard_period`: `L_{i+1} = ϖ L_i = 𝔭 L_i`, so `e = 1` by uniqueness of the
period (`LatticeChain.period_unique`).

`levelSubgroup_le_unitSubgroup`: let `g` be the image of `h ∈ GL_1(𝒪_K)` with
`d = h₀₀ - 1 ∈ 𝔭^c`. By `mem_unitSubgroup_iff_sub_one_mem` and `toLin'_sub_one_rankOne` it
suffices that `d · 1 ∈ 𝔓^{m+1}(𝓛)`. If `d = 0` this is clear. Otherwise `d · 1 ∈
𝔓^{e(𝓛) ordOf(d)}(𝓛)` (`LatticeChain.smul_mem_endFiltration_ordOf`, module `CompactLevelBound`), and
`e(𝓛) ordOf(d) ≥ e(𝓛) c ≥ m + 1`.

`unitSubgroup_standard_le_levelSubgroup`: if `g ∈ U^c(𝔄)`, then `(g - 1) L_0 ⊆ L_c`; applied to
the vector `1 ∈ L_0` this gives `d = g₀₀ - 1 ∈ ϖ^c 𝒪_K`. Then `d ∈ 𝔭^c ⊆ 𝔭`, so `1 + d` is a
unit of `𝒪_K`; the scalar matrix `1 + d` in `GL_1(𝒪_K)` lies in the congruence subgroup of
`𝔭^c` (`Conductor.mem_integralCongruence_rankOne`) and maps to `g`.

`hasFixedVector_of_le_rankOne`: fixed vectors are antitone in the subgroup (`fixedVectors_antitone`).

`exists_firstFixedLevel_eq_of_isNormalizedLevel_rankOne`: choose a uniformizer `ϖ`.

1. Since `x` is attained, there are a lattice chain `𝓛₀` of period `e₀` and `m₀` with
   `x = m₀ / e₀` and a nonzero `U^{m₀+1}(𝔄(𝓛₀))`-fixed vector. With `q = ⌊m₀ / e₀⌋`,
   `m₀ + 1 ≤ e₀ (q + 1)`, so `levelSubgroup_le_unitSubgroup` gives a nonzero vector fixed by
   the level subgroup at `q + 1`. Hence (`firstFixedLevel_le_iff`, Library) the first fixed level
   is at most `q + 1`; in particular it is a natural number `c`.
2. Upper bound: `c - 1 ≤ q ≤ m₀ / e₀ = x`.
3. Lower bound: the class has a nonzero vector fixed by the level subgroup at `c`, hence at
   `max(c, 1)` (`levelSubgroup_antitone`), hence by `U^{max(c,1)}(𝔄)` of the standard chain
   (`unitSubgroup_standard_le_levelSubgroup`). As the standard chain has period `1`,
   `max(c, 1) - 1 = c - 1` is a normalized level value, and minimality of `x` gives
   `x ≤ c - 1`.
