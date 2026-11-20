# The Swan conductor and the normalized level in rank at least two

Lean proof by Worker 408 for Task 7683.

## Setting

`K` is a `p`-adic field with its canonical topology, valuation and measurable structure (local
instances `slr*`, as in the related proof modules). `GeneralLinear.SupercuspidalClass
(n := n + 1)` is the Library's type of isomorphism classes of irreducible supercuspidal
representations of `GL_{n+1}(K)`; `toSmoothDualClass` forgets supercuspidality, and
`firstFixedLevel` is the least `m` such that the class has a nonzero vector fixed by the
Library's level subgroup `K_1(𝔭^m)` (value in `WithTop ℕ`, `⊤` if there is none). This first
fixed level is the conductor `Henniart.Numerical.conductor` of the target statement T2.
`IsNormalizedLevel K N a x` (Library, Task 7419) says that `x` is the least element of the set of
values `m / e(𝓛)` with `𝓛` a lattice chain in `K^N` of period `e(𝓛)` and `a` having a nonzero
vector fixed by `U^{m+1}(𝔄(𝓛))` (Bushnell 1987, (3.3)).

## Declarations

- `natSub_eq_of_max_eq`: for natural numbers `c`, `N` and a rational `x`, if
  `max(c, N) = N (1 + x)` in `ℚ`, then the truncated difference `c - N` equals `N x`.
- `exists_firstFixedLevel_eq_of_isNormalizedLevel` (T2 in rank at least two): let `n ≥ 1` and
  `π` an irreducible supercuspidal class of `GL_{n+1}(K)` whose underlying class has normalized
  level `x`. Then the first fixed level of `π` is a natural number `c`, and
  `c - (n + 1) = (n + 1) x` with truncated subtraction.

## Provenance

The formula `a(π) = N (1 + ℓ(π))` for a supercuspidal representation `π` of `GL_N(K)`,
`N ≥ 2`, with `a(π)` the conductor and `ℓ(π)` the normalized level, is Bushnell (1987),
Theorem 3, printed p. 198, together with Bushnell–Fröhlich (1985), (3.3.8), printed p. 258;
operator route note, Proposition `prop:T2`. The proof uses the determinant-shell calculation
of `ConductorFormula` and takes the truncated difference as in the Library's T2 statement.

## Proof

`natSub_eq_of_max_eq`: if `c ≤ N` the maximum is `N`, so `N x = 0` and both sides are `0`; if
`N ≤ c` the maximum is `c` and `c - N = N x` in `ℚ`.

`exists_firstFixedLevel_eq_of_isNormalizedLevel`: choose a representative `A` of `π`.

1. The Library theorem `padicUnitaryAdditiveCharacterExists` gives a nontrivial unitary
   additive character `ψ₀` of `K`; `RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor`
   gives a unit `u` such that `ψ = ψ₀.scale u` has conductor `𝔬_K`; and
   `RankinSelberg.HighlyRamified.nonempty_selfDualHaar` gives a measure `ν` self-dual for `ψ`.
2. The Library theorem `GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData`
   (rank greater than one) gives Godement–Jacquet functional-equation data of `A` with both Euler
   polynomials `1`, a unit `c` and an exponent `a ∈ ℤ`.
3. `max_exponent_eq_of_isNormalizedLevel` (module `ConductorFormula`) gives
   `max(a, n + 1) = (n + 1)(1 + x)`.
4. `exists_exponent_eq_firstFixedLevel` (module `ConductorBridge`) gives `m : ℕ`
   with `a = m` and `firstFixedLevel π = m`.
5. With `c = m`, `natSub_eq_of_max_eq` turns step 3 into `m - (n + 1) = (n + 1) x`.

The additive character and the measure are chosen inside the proof, so the theorem has no
additive-character premise.
