# The functional-equation exponent of a supercuspidal representation and its level

## Setting

As in `ConductorUpperBound` and `ConductorLowerBound`: `K` is a `p`-adic field with canonical
order `T.ord` (`T = K.canonicalTopologicalData`), `N = n + 1`, `ψ` is a
`UnitaryAdditiveCharacter K.Carrier` and `ν` an `AdditiveHaarMeasure K.Carrier`.
`Conductor.HasIntegerConductor ψ` (Library) says that `ψ` is trivial on `𝔬_K` and that every
`t` with `ψ(t y) = 1` for all `y ∈ 𝔬_K` lies in `𝔬_K`; that is, `ψ` has conductor `𝔬_K`.
`IsSelfDual ψ ν` (Library) says that `ν` is self-dual for `ψ`.
`GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a` is the Library's
Godement–Jacquet functional equation for `σ` with both Euler polynomials `1`, unit `c` and
exponent `a`. `𝓛` is a lattice chain in `K^N` with period `e = 𝓛.period`,
`𝔓^j(𝓛) = 𝓛.endFiltration j` and `U^k(𝔄(𝓛)) = unitSubgroup K 𝓛 k`. `IsNormalizedLevel K N a x`
and `ContainsStratum` are the published definitions of the Library module
`Langlands.BushnellKutzko.NormalizedLevel`.

## Declarations

- `scaledCharacter K ψ t`: the additive character `x ↦ ψ(t x)` of `K`, with values in `ℂ`.
  `scaledCharacter_apply` unfolds it.
- `scaledCharacter_eq_one_of_mem_maximalIdeal`: if `ψ` has conductor `𝔬_K` and `ϖ` is a
  uniformizer, then `x ↦ ψ(ϖ⁻¹ x)` is trivial on `𝔭_K`.
- `exists_scaledCharacter_ne_one`: under the same hypotheses, `x ↦ ψ(ϖ⁻¹ x)` is nontrivial on
  `𝔬_K`. Together with the previous item, `ψ(ϖ⁻¹ ·)` is a character of level one in the sense of
  `ContainsStratum`.
- `elementCharacter_scaledCharacter`: for an endomorphism `b` of `K^N` with matrix `B` and
  `g ∈ GL_N(K)`, `ψ(t tr(b (g - 1))) = ψ(tr((t B)(g - 1)))`.
- `exponent_le_of_fixedVector` (level zero): if `σ` is a smooth representation of `GL_N(K)`
  with the functional-equation data above, `ψ` has conductor `𝔬_K`, and `σ` has a nonzero vector
  fixed by `U^1(𝔄(𝓛))` for some lattice chain `𝓛`, then `a ≤ N`.
- `period_mul_exponent_eq_of_stratum` (positive level): if `ψ` has conductor `𝔬_K`, `ϖ` is a
  uniformizer, `σ` is irreducible and supercuspidal with the functional-equation data above,
  `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`, no power `b^i` lies in `𝔓^{1-im}(𝓛)`, and a nonzero `v` satisfies
  `σ(g) v = ψ(ϖ⁻¹ tr(b (g - 1))) v` for all `g ∈ U^m(𝔄(𝓛))`, then `e a = N m + e N`.
- `max_exponent_eq_of_isNormalizedLevel` (the main theorem): let `ψ` have conductor `𝔬_K`, `ν`
  be self-dual for `ψ`, and `A` an irreducible supercuspidal representation of `GL_N(K)`
  (a Library `GeneralLinear.SupercuspidalRep`) whose representation has the functional-equation
  data above. If the class of `A` has normalized level `x`, then

  `max(a, N) = N (1 + x)` (in `ℚ`).

  So `a ≤ N` if `x = 0`, and `a = N (1 + x)` if `x > 0`.

The theorem takes the functional-equation data as a hypothesis. The Library supplies such data
for irreducible supercuspidal representations of `GL_N(K)` with `N ≥ 2`
(`GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData`). `ConductorBridge`
identifies `a` with the conductor `Numerical.conductor` of the target statement.

## Provenance

For `x > 0` the equality `a = N (1 + x)` recovers the exponent formula of Bushnell (1987),
Theorem 3, and Bushnell–Fröhlich (1985), (3.3.8). At `x = 0`, the bound `a ≤ N` suffices
for T2's truncated difference to vanish. The declarations are internal to the
determinant-shell proof of T2.

## Proof

`scaledCharacter_eq_one_of_mem_maximalIdeal`: an element of `𝔭_K` is `y ϖ` with `y ∈ 𝔬_K`, so
`ψ(ϖ⁻¹ y ϖ) = ψ(y) = 1`.

`exists_scaledCharacter_ne_one`: if `ψ(ϖ⁻¹ y) = 1` for all `y ∈ 𝔬_K`, the conductor hypothesis
puts `ϖ⁻¹` in `𝔬_K`, but `ord(ϖ⁻¹) = -1`.

`elementCharacter_scaledCharacter`: identify `g` with the endomorphism `toLin' g`, write
`b (toLin' g - 1)` as `toLin'` of `B (g - 1)` and use `Matrix.trace_toLin'_eq` and
`Matrix.trace_smul`.

`exponent_le_of_fixedVector`: choose a smooth functional `ℓ` with `ℓ(v) ≠ 0`
(`exists_smoothDual_apply_ne_zero_of_compact_cofinal`, Library) and a uniformizer `ϖ`. The fixed
vector is a stratum vector for `b' = 0` and `k = 1`. Apply `period_mul_le_of_stratum` (module
`ConductorUpperBound`) with `t = ϖ⁻¹` and `j = 0`. It gives `e a ≤ -e N ord(ϖ⁻¹) = e N`, so
`a ≤ N` because `e > 0`.

`period_mul_exponent_eq_of_stratum`: choose `ℓ` with `ℓ(v) ≠ 0` as before and put
`b' = ϖ⁻¹ B`. By `elementCharacter_scaledCharacter`, `σ(g) v = ψ(tr(b'(g - 1))) v` on
`U^m(𝔄(𝓛))`, and `t⁻¹ b' = B` for `t = ϖ⁻¹`. The Library theorem
`GodementJacquet.exists_centralCharacter_compactScalarSupport` gives a compact set `C` such that
`h ↦ ℓ(σ(h) v)` vanishes outside the scalar saturation of `C`. Then `period_mul_eq_of_stratum`
(module `ConductorLowerBound`) with `k = m` gives `e a = N m - e N ord(ϖ⁻¹) = N m + e N`.

`max_exponent_eq_of_isNormalizedLevel`: the self-dual measure is σ-finite
(`selfDualSigmaFinite`, Library). Since `x` is a normalized level, `x = m₀/e₀ ≥ 0` for some
chain of period `e₀ > 0`.

- If `x = 0`, then `m₀ = 0`, so the class has a nonzero vector fixed by `U^1(𝔄(𝓛₀))`. The
  class is that of `A`, so `A` itself has such a vector, and `exponent_le_of_fixedVector` gives
  `a ≤ N`, hence `max(a, N) = N = N (1 + 0)`.
- If `x > 0`, `exists_containsStratum_of_isNormalizedLevel` (module `StratumExistence`, with the
  level-one character `ψ(ϖ⁻¹ ·)`) gives `𝓛`, `m` and `b` with `x = m/e` and the stratum
  `[𝔄(𝓛), m, m - 1, b]` contained in the class. `pow_add_not_mem_of_isNormalizedLevel` (module
  `LevelAttainingStratum`, with `y = 0`) gives `b^i ∉ 𝔓^{1-im}(𝓛)` for every `i`. The stratum
  vector lives in a representative `A'` of the class; transport it to `A` along the
  isomorphism `A' ≅ A` (`SmoothRep.equivOfIso`, Library), which is injective and intertwines the
  actions. `period_mul_exponent_eq_of_stratum` gives `e a = N m + e N`, so
  `a = N (1 + m/e) = N (1 + x) ≥ N`, and `max(a, N) = a`.
