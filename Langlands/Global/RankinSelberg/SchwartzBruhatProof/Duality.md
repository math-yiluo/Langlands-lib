# Duality of the finite-adelic lattices under a standard character

Module `Langlands.Global.RankinSelberg.SchwartzBruhatProof.Duality`, namespace
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`. It is a supporting module for
the proof of `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`.

## Provenance

These are internal lemmas. They globalize the local lattice duality of the Library:
`Langlands.PadicField.TopologicalData.forall_mul_eq_one_iff_mem_additiveLattice` states that the
`ψ_v`-annihilator of `ϖ_v^(-k) 𝒪_v` is `ϖ_v^(-(n(ψ_v) - k)) 𝒪_v`. The globalization uses the
Library's local components and conductor divisor of a global additive character (from the Hecke
functional equation modules, `HeckeFunctionalEquation.*`) and the product formula
`HeckeFunctionalEquation.finite_additive_product`. This duality is the finite-adelic input of
the self-duality in Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Lemma C.3.1 and (C.6), printed p.554, and of Tate's thesis §4.1. The Lean proofs are written for
this formalization.

## Declarations

Fix `ψ : AddChar (Adeles F) ℂ` with `IsStandardAdditiveCharacter F ψ`. Write
`ψ_f = EqualAnalytic.finiteCharacter F ψ`, which is `t ↦ ψ(finiteAdele F t)` on `𝔸_f`.

- `standardUnitary ψ hψ`: `ψ` as a Library `UnitaryAdditiveCharacter` of `𝔸`, with
  `coe_standardUnitary_apply` and `standardUnitary_diagonal` (trivial on `F`).
- `localComponent ψ hψ v`: the local component at a finite place `v`
  (`HeckeFunctionalEquation.globalFiniteAdditiveComponent`), with `coe_localComponent_apply`.
- `conductorDivisor ψ hψ = n_ψ`: the Library's `HeckeFunctionalEquation.additiveConductorDivisor`,
  whose value at `v` is the additive conductor `n(ψ_v)` of the local component
  (`conductorDivisor_apply`). The remaining arguments are the Library's archimedean scale data.
- `finiteCharacter_zero`, `continuous_finiteCharacter`, `finiteCharacter_sum` (additivity over
  finite sums), `finiteCharacter_inclusion` (`ψ_f` on a single local coordinate is the local
  component), and `finiteCharacter_eq_prod` (`ψ_f(t) = ∏_(v ∈ S) ψ_v(t_v)` for `S` containing
  the control set of `ψ` and the non-integral places of `t`).
- `forall_finiteCharacter_eq_one_iff` (**lattice duality in `𝔸_f`**): for
  `m : FinitePlace F →₀ ℤ` and `η ∈ 𝔸_f`, `ψ_f(t η) = 1` for all `t ∈ L_m` iff
  `η ∈ L_(n_ψ - m)`.
  - (`⇒`) Test with `t` supported at the single place `v`. Then `ψ_f(t η) = ψ_v(t_v η_v)`, and
    local duality gives `η_v ∈ L_v(n(ψ_v) - m v)`.
  - (`⇐`) Write `ψ_f(t η)` as a finite product of local values, each `1` by local duality.
- `finiteCharacter_eq_one_of_mem`: `ψ_f` is trivial on `L_(n_ψ)` (the case `m = n_ψ`, `η = 1`).
  Hence `isLocallyConstant_finiteCharacter`.
- `forall_finiteCharacter_sum_eq_one_iff` (**lattice duality in `𝔸_f^n`**): the annihilator of
  `L_m^n` under `(u, η) ↦ ψ_f(Σ_j u_j η_j)` is `L_(n_ψ - m)^n`. Test with `u = Pi.single j t`
  for one direction; use `finiteCharacter_sum` for the other.
