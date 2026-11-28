# Intertwined pure strata of depth `n − 1` are conjugate

This module proves the case `t = n − 1` of the proof of BK93 (2.6.1). It also proves the
final step of the induction there, in which two cosets, each pure or null, are compared.

Source: Bushnell–Kutzko (1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`,
(2.6.1), printed pp. 83–86 (PDF pp. 95–98). The case `t = n − 1` is on pp. 83–84. The
three cases of the induction step are on pp. 85–86. The notation is that of
`SimpleStratumConjugacyUnits`. `SymbolEq 𝓛 d x y` says that `x, y ∈ 𝔓^d` and
`x − y ∈ 𝔓^{d+1}`.

## Results

- `exists_conj_symbol_of_intertwined`: let `A₁, A₂` be units shifting the chain by `d`,
  such that every nonzero element of `F[A_i]` is a unit normalizing the chain. Suppose
  `x ≡ A₂` and `g⁻¹ x g ≡ A₁` in degree `d` for some `x` and `g`. Then a unit `u` of `𝔄` satisfies
  `u A₂ u⁻¹ ≡ A₁` in degree `d`.
- `exists_conj_of_isPure`: let `[𝔄,n,r,β_i]` be pure strata on the same chain with the same
  `n`. If some `g` carries an element of `β₂ + 𝔓^{1−n}` into `β₁ + 𝔓^{1−n}`, then a unit
  `u` of `𝔄` satisfies `u β₂ u⁻¹ ∈ β₁ + 𝔓^{1−n}`.
- `PureOrNull 𝓛 n c` (internal notation): the coset `c + 𝔓^{1−n}` is that of a unit `B`
  shifting the chain by `−n` such that every nonzero element of `F[B]` is a unit
  normalizing the chain, or it is `𝔓^{1−n}`.
  `pureOrNull_of_isPure` and `pureOrNull_of_scalar` give the two sources of such cosets
  used in BK93: cosets of pure strata, and cosets of scalars lying in `𝔓^{−n}`.
- `exists_conj_of_pureOrNull`: two intertwined cosets `c_i + 𝔓^{1−n}`, each pure or
  null, are conjugate by a unit of `𝔄`.
- Helpers: `residual_mem_elementAlgebra`, `residual_symbolEq`, `residual_conj`,
  `conj_mem_of_shifts_zero`, `shifts_eq_of_mem`, `scalar_shifts`,
  `normalizingUnits_algebraMap`.

## Proof of `exists_conj_symbol_of_intertwined`

Let `π` be a uniformizer and `e` the period. Write `g₀ = gcd(e, d)`, `e = h g₀`,
`d = k g₀` and `u k + v h = 1` (`ShiftParameters`). The units `z_i = A_i^h π^{−k}` and
`τ_i = A_i^u π^v` lie in `F[A_i]`. They shift the chain by `0` and `g₀`, commute, and
satisfy `τ_i^h = π z_i^u` and `A_i = τ_i^k z_i^v`.

1. `exists_residual_polynomial_of_normalizing` gives `Q` with `Q(z₁) ∈ 𝔓`. The
   intertwining makes `x` a unit `X` with `N.residual X π ≡ z₂`, and conjugation by
   `g` gives `≡ z₁` (`residual_conj`). Then `aeval_mem_one_of_conj` gives
   `Q(z₂) ∈ 𝔓`.
2. `exists_cyclicBasis_count` gives cyclic bases `B_i` for `(z_i, τ_i)` with the same
   polynomial `Q`. Their numbers of generators agree because both are dimensions of the
   same layers divided by `deg Q`. One cyclic algebra `M` with the relations
   `Q(U) = 0` and `T^h = π U^u` serves both bases (`exists_cyclicAlgebra`).
3. `exists_unit_conj_action` gives a unit `u` of `𝔄` with `u U'₂ u⁻¹ = U'₁` and
   `u T'₂ u⁻¹ = T'₁` for the transported actions `U'_i, T'_i` of the roots.
   `actionU_symbol` and `actionT_symbol` give `U'_i ≡ z_i` in degree `0` and `T'_i ≡ τ_i`
   in degree `g₀`. Hence `u z₂ u⁻¹ ≡ z₁` and `u τ₂ u⁻¹ ≡ τ₁`.
4. `ShiftParameters.lifted_symbol` and `ShiftParameters.reconstruct` give
   `u A₂ u⁻¹ = (u τ₂ u⁻¹)^k (u z₂ u⁻¹)^v ≡ τ₁^k z₁^v = A₁` in degree `d`.

The source compares the polynomials `φ_{α_i}`. The strata `[𝔄,n,n−1,α_i]` are nonsplit
fundamental by (2.3.2), and (2.5.11), printed pp. 82–83, conjugates them by units of `𝔄`
to strata equivalent to strata in standard form for a common matrix. Since these strata
are equivalent to simple strata, (2.5.8), printed p. 80, shows that the blocks of the
standard forms are semisimple. With Remark (ii) preceding (2.5.8), the first standard
form is then equivalent to a `U(𝔄)`-conjugate of the second. The Lean argument uses
neither normal form and needs only purity of the two strata.

## Proof of `exists_conj_of_pureOrNull`

If both cosets are pure, the units `B_i` satisfy the hypotheses of
`exists_conj_symbol_of_intertwined`. If both are null, `u = 1`. In the mixed cases the
intertwining would conjugate an element of `B + 𝔓^{1−n}` into `𝔓^{1−n}`, contradicting
`conj_not_mem_of_shifts`. These are the three cases on BK93 printed pp. 85–86; the mixed
case is excluded in the source by (2.6.2).

For `pureOrNull_of_scalar`, a nonzero scalar `δ` shifts the chain by `e · ord(δ)`
(`scalar_shifts`). If `δ ∈ 𝔓^{−n} ∖ 𝔓^{1−n}` this shift is `−n` (`shifts_eq_of_mem`).
`F[δ] = F`, and every nonzero element of `F` is a unit normalizing the chain
(`normalizingUnits_algebraMap`).
