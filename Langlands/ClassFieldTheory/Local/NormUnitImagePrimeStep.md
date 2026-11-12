# Level claims for unramified and for prime-degree abelian extensions

Helper module for the proof of
`Langlands.LocalClassField.FiniteAbelianNormUnitImageCardinality`. It proves
the internal `LevelClaims K L` of `NormUnitImageTower` in two base cases:

- `levelClaims_of_ramificationIndex_eq`: `L/K` is finite abelian and
  unramified;
- `levelClaims_of_prime`: `L/K` is abelian of prime degree `ℓ`.

Throughout, `K : PadicField.{u} p` and `L : PadicField.{v} p` carry their
canonical topological data `TK` and `TL`, the extension is compatible with
`ℚ_p`, and `N = normUnits K L`. The mathematics is the prime-degree analysis of
Serre, *Local Fields*, Chapter V, §§3 and 6. Its norm computations come from
published Library statements; this module only assembles them into the
divisibility claims.

## Real-level bookkeeping

- `ceil_le_of_eq_natCast`, `lt_ceil_of_eq_natCast`: let `ψ : ℝ → ℝ` agree on
  naturals with `P : ℕ → ℕ`. If `ψ` is monotone, then `⌈ψ a⌉₊ ≤ P ⌈a⌉₊`. If
  `ψ` is strictly monotone and `⌈a⌉₊ > 0`, then `P (⌈a⌉₊ - 1) < ⌈ψ a⌉₊`.
  Both follow from `a ≤ ⌈a⌉₊ < a + 1`.
- `herbrandPsi_nonneg`: `ψ_{L/K}(a) ≥ 0` for `a ≥ 0`, because `ψ` is strictly
  increasing with `ψ(0) = 0`.
- `upperRamificationGroup_eq_lowerRamificationGroup_ceil`: for `a ≥ 0`,
  `G^a = G_m` with `m = ⌈ψ_{L/K}(a)⌉₊`. This is the definition
  `G^a = G_{ψ(a)}` (`Padic.upperRamificationGroup_eq_lower`) together with the
  fact that a real lower index is used through its ceiling.
- `herbrandPsi_eq_self_of_lower_eq_bot`: if every lower group `G_i`, `i ∈ ℕ`,
  is trivial, then `ψ_{L/K}(a) = a` for `a ≥ 0`. All lower orders are `1`, so
  the explicit formula `Padic.herbrandPhi_floor` gives `φ(a) = a`. Then
  `ψ(a) = ψ(φ(a)) = a`.

## The unramified case

The hypothesis is the equality of absolute ramification indices
`TK.ramificationIndex = TL.ramificationIndex`.

- `inertia_eq_bot_of_ramificationIndex_eq` (Galois `L/K`): the inertia group
  is trivial. If `σ ∈ G_0`, then `σ(x) - x` lies in the maximal ideal for
  every integer `x` of `L` (`Padic.mem_lowerRamificationGroup`). The integer
  ring `LocalGalois.extensionIntegers K L` of the spectral norm has the same
  elements as the canonical one (`ArithmeticCoordinate.extensionIntegerEquiv`).
  So the residue automorphism `LocalGalois.residueHom K L σ` is the identity.
  This residue map is injective in the unramified case
  (`ArithmeticCoordinate.residueHom_injective`), hence `σ = 1`. The module
  declares, as local instances, the canonical normed-field structure on `K`
  used in the statement of that lemma.
- `levelClaims_of_ramificationIndex_eq` (abelian `L/K`): every lower group is
  contained in `G_0 = 1`. So `ψ(a) = a`, `m = ⌈a⌉₊ = n` and `G^a = G_n = 1`.
  The norm maps `U_L^n` onto `U_K^n` (`unramifiedUnitNorms`). Then (C) is
  equality, the relative index in (V) is `1`, and in (WZ)
  `[Kˣ : U_K^n · N(Lˣ)]` divides `[Kˣ : N(Lˣ)] = [L : K]`
  (`normSubgroup_index_eq_finrank`).

## Prime degree

Let `ℓ = [L : K]` be prime.

- `ramificationIndex_eq_or_of_prime`: either `e(L) = e(K)` or
  `e(L) = ℓ · e(K)` for the absolute ramification indices. Let `c` be the
  normalized order in `L` of a uniformizer of `K`. Then `e(K) · c = e(L)`
  (`ramificationIndex_mul_ord_relative_algebraMap`). With `f` the relative
  residue degree, `e(L) · f = ℓ · e(K)`
  (`PadicField.ramificationIndex_mul_extensionResidueDegree` and
  `extensionDegree_suppliedAlgebra`). Hence `c · f = ℓ` with `c > 0`, so `c`
  is `1` or `ℓ`.
- `units_eq_one_of_pow_char_eq_one`: in a field of characteristic `p`, a unit
  `ξ` with `ξ^p = 1` equals `1`, since `(ξ - 1)^p = ξ^p - 1 = 0`.
- `levelClaims_of_prime`: the first alternative is the unramified case. The
  second is `levelClaims_of_totallyRamified` below.

### The totally ramified case

Assume `e(L) = ℓ · e(K)`. The published statement `primeTotallyRamifiedBreak`
gives the break `t`: `G_i = G` for `i ≤ t` and `G_i = 1` for `i > t`; also
`t > 0` iff `ℓ = p`, and at naturals `ψ(k) = P(k)`, where
`P(k) = k` for `k ≤ t` and `P(k) = t + ℓ(k - t)` otherwise. The proof also uses
the following published statements.

- `primeRamifiedNormReduction`:
  - `N(U_L^{P(k)}) = U_K^k` for `k > t`;
  - `N(U_L^{P(k)+1}) = U_K^{k+1}` for `k ≥ t`;
  - every `x ∈ Kˣ` is `N(y) · z` with `z ∈ U_K^t`.
- `primeRamifiedGradedNorm`:
  - `N(U_L^{P(k)}) ≤ U_K^k`;
  - the zero-level formula `r(ζ_K(N y)) = ζ_L(y)^ℓ` for the residue
    coordinates `ζ` of units and the relative residue map `r`;
  - for `0 < k < t`, the coefficient formula
    `r(res c_k(N y)) = r(res a) · res(c_k(y))^p` with `res a ≠ 0`. Here `c_k`
    is the `k`th unit coefficient with respect to fixed uniformizers.
- `ord_normUnits_of_totalRamification`: `ord_K(N y) = ord_L(y)`.

Fix `a ≥ 0` and put `n = ⌈a⌉₊` and `m = ⌈ψ(a)⌉₊`, so `G^a = G_m`. The
real-level bookkeeping gives `m ≤ P(n)`, and `P(n - 1) < m` when `n > 0`.

**Below the break, `n ≤ t`.** Then `P(n) = n`, which forces `m = n`. So
`G^a = G_n = G` has order `[L : K] = ℓ` (`IsGalois.card_aut_eq_finrank`).

- (C) is the containment `N(U_L^{P(n)}) ≤ U_K^n`.
- Lifting: for `k ≤ t` and `y ∈ Lˣ`, `N(y) ∈ U_K^k` implies `y ∈ U_L^k`. The
  proof is by induction on `k`. At `k = 0`, `ord_L(y) = ord_K(N y) = 0`. For
  the step to `k + 1 ≤ t`, we know `y ∈ U_L^k`. If `k = 0`, then
  `ζ_K(N y) = 1`, so `ζ_L(y)^ℓ = 1`. Here `t > 0` gives `ℓ = p`, and the
  characteristic-`p` lemma gives `ζ_L(y) = 1`, that is `y ∈ U_L^1`. If
  `0 < k < t`, the `k`th coefficient of `N y` has zero residue. Because `r` is
  an injective ring map and `res a ≠ 0`, we get `res(c_k(y))^p = 0`, so
  `y ∈ U_L^{k+1}`.
- So `N(U_L^n) = U_K^n ⊓ N(Lˣ)`. For (V), its relative index in `U_K^n` equals
  the relative index of `N(Lˣ)` in `U_K^n`. This divides
  `[Kˣ : N(Lˣ)] = ℓ = |G^a|`.
- (WZ): `U_K^n ⊇ U_K^t`, and `U_K^t · N(Lˣ) = Kˣ` by the third reduction
  clause. So the index is `1`, and `1 · ℓ` divides `ℓ`.

**Above the break, `n > t`.** Then `m > P(n - 1) ≥ t`, so `G^a = G_m = 1`.
Moreover `N(U_L^m) = U_K^n`. On one side,
`N(U_L^m) ≤ N(U_L^{P(n-1)+1}) = U_K^n`. On the other,
`U_K^n = N(U_L^{P(n)}) ≤ N(U_L^m)`. Now (C) and (V) are immediate, and (WZ)
holds because `U_K^n · N(Lˣ)` contains `N(Lˣ)`, whose index is `ℓ`.
