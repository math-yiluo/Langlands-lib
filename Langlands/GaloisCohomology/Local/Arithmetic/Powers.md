# `n`-th powers in a nonarchimedean local field

`Langlands/GaloisCohomology/Local/Arithmetic/Powers.lean`, namespace
`Langlands.GaloisCohomology.Local`.

For a nonarchimedean local field `K` (Mathlib's `IsNonarchimedeanLocalField`) and an integer `n`
invertible in `K`, the subgroup `Kˣⁿ` of `n`-th powers is open and of finite index in `Kˣ`. Both
come from Hensel's lemma: every unit congruent to `1` modulo `n² π` is an `n`-th power
(the Library's `ClassFieldTheory.Global.exists_one_add_mul_mul_pow_eq`, valid in any adically
complete ring), together with the decomposition `x = π^{ord x} · u` of a unit of `K` (the
Library's normalized order `normalizedUnitOrder` and uniformizer `localUniformizer`).

## Declarations

- `integerUnitOfValuationEqOne x hx`: a unit of `K` of valuation `1` as a unit of `𝒪[K]`
  (`coe_integerUnitOfValuationEqOne`); `integerUnitsMap K : 𝒪[K]ˣ →* Kˣ`
  (`coe_integerUnitsMap_apply`, `integerUnitsMap_injective`, `valuation_integerUnitsMap`).
- `integerCongruenceUnits K I`: the units of `𝒪[K]` congruent to `1` modulo the ideal `I`
  (`mem_integerCongruenceUnits_iff`); of finite index for `I ≠ ⊥`
  (`integerCongruenceUnits_finiteIndex`, from `finite_quotient_integer`).
- `isAdicComplete_integer K`: `𝒪[K]` is `𝓂`-adically complete.
- `valuation_unit_mul_zpow_neg_eq_one`, `unitPart K : Kˣ →* 𝒪[K]ˣ` (`x ↦ x · π^{-ord x}`) and
  `integerUnitsMap_unitPart_mul`: `x = unitPart x · π^{ord x}`.
- `integerCongruenceUnits_le_range_pow hn hc`: for `n ≠ 0` and `c ∈ 𝓂`, units congruent to `1`
  modulo `n² c` are `n`-th powers of units.
- `integerUniformizer` (`π` in `𝒪[K]`, in `𝓂`, nonzero: `integerUniformizer_mem_maximalIdeal`,
  `integerUniformizer_ne_zero`), `powerCongruenceIdeal n = (n² π)` (`powerCongruenceIdeal_ne_bot`
  for `n` invertible in `K`), `integerUnitsMap_mem_range_pow`.
- `powerTestHom K n : Kˣ → ℤ/n × (𝒪[K]/(n²π))ˣ`, `x ↦ (ord x mod n, unitPart x mod n²π)`, with
  `ker_powerTestHom_le`: its kernel consists of `n`-th powers.
- `finiteIndex_range_powMonoidHom hn`, `finite_quotient_range_powMonoidHom hn`: for
  `(n : K) ≠ 0`, `Kˣⁿ` has finite index, `Kˣ/Kˣⁿ` is finite.
- `isOpen_map_integerCongruenceUnits hc hc0`: the units `≡ 1 mod c` (`0 ≠ c ∈ 𝓂`) form an open
  subset of `Kˣ`; `isOpen_range_powMonoidHom hn`: for `(n : K) ≠ 0`, `Kˣⁿ` is open in `Kˣ`.

## Source and licence

New file. The two statements are those of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`:
`finite_quotient_range_pow` (`src/GroundTheory/LocalFields/UnitsPowers.lean`) and
`isOpen_range_pow` (`src/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean`),
used by the source's local Galois cohomology. The source proves them with its own unit filtration,
Teichmüller lifts and root-finding lemma; the proofs here are new, on the Library's normalized
order and its Hensel lemma for powers, and contain no text of the source.

## References

- J. Neukirch, *Algebraic Number Theory*, chapter II, §5, Corollary (5.8) (`(K* : K*ⁿ) = n · #μₙ(K)
  / |n|` for `n` prime to the characteristic), p. 142.
