# The unit filtration of a nonarchimedean local field

`Langlands/GaloisCohomology/Local/Arithmetic/Units.lean`, namespace `Langlands.GaloisCohomology.Local`.

The units `𝒪[K]ˣ` of a nonarchimedean local field with the filtration `U^n = 1 + 𝓂^n` (the NYLL
copy's `LocalFieldTheory.principalUnits`), the description of `𝓂^n` by a uniformizer, the
reduction of units to the residue field, and the extraction of roots of principal units by
Hensel's lemma (the Library's `exists_isRoot_of_isAdicComplete` and
`exists_one_add_mul_mul_pow_eq`).

## Declarations

- `unitFiltration K n` (abbreviation of NYLL's `principalUnits K n`), `mem_unitFiltration`,
  `unitFiltration_zero`, `unitFiltration_antitone`; instance `unitFiltration_finiteIndex`
  (`U^n` is the kernel of `𝒪[K]ˣ → (𝒪[K]/𝓂^n)ˣ`).
- `unitsToResidue K : 𝒪[K]ˣ →* 𝓀[K]ˣ`, `ker_unitsToResidue` (`= U¹`).
- `mem_maximalIdeal_pow_iff hϖ : x ∈ 𝓂^n ↔ ϖⁿ ∣ x`, `mem_maximalIdeal_iff_dvd`,
  `uniformizer_mem_maximalIdeal`, `exists_sub_one_eq_mul`.
- `valuation_unit`, `valuation_lt_one_of_mem_maximalIdeal`, `isUnit_unit_add`,
  `mem_range_integerUnitsMap_iff`: a unit of `K` is in `𝒪[K]ˣ` iff its valuation is `1`.
- `exists_pow_eq_of_mem_unitFiltration_one hm hw`: for `m` invertible in `𝓀[K]`, every principal
  unit is the `m`-th power of a principal unit.
- `exists_pow_eq_of_mem_unitFiltration hϖ hp hpe hk hw`: for `p = ϖ^e ε` prime and `k ≥ e + 1`,
  every unit of `U^{k+e}` is the `p`-th power of a unit of `U^k`.

## Source and licence

Partly ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`: `mem_maximalIdeal_pow_iff`, `mem_maximalIdeal_iff_dvd`,
`uniformizer_mem_maximalIdeal`, `exists_sub_one_eq_mul`, `valuation_unit`,
`valuation_lt_one_of_mem_maximalIdeal`, `unitsToResidue`, `ker_unitsToResidue` from
`src/GroundTheory/LocalFields/UnitsBasic.lean`; `isUnit_unit_add` from `UnitsPowers.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Changes: the source's `unitFiltration` is bound to the NYLL copy's `principalUnits` (definition
not copied). `mem_range_integerUnitsMap_iff` (source `mem_range_unitsIncl_iff`) is stated with the
valuation instead of the source's normalized valuation. The two root-extraction theorems have the
statements of the source's `exists_pow_eq_of_mem_unitFiltration_one` and
`exists_pow_eq_of_mem_unitFiltration`
(`src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsPower.lean`), with new proofs
on the Library's Hensel lemmas in place of the source's `exists_root_of_dvd`;
`unitFiltration_finiteIndex` has a new proof.

## References

- J.-P. Serre, *Local Fields*, chapter IV, §2, Proposition 6 (the quotients `U⁰/U¹` and `Uⁱ/Uⁱ⁺¹` of
  the unit filtration), p. 65.
