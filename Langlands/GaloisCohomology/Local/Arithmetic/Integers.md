# Rings of integers of finite extensions of local fields

`Langlands/GaloisCohomology/Local/Arithmetic/Integers.lean`, namespace `Langlands.GaloisCohomology.Local`.

For a finite extension `L/K` of nonarchimedean local fields, `𝒪[L]` is a finite free `𝒪[K]`-module
of rank `[L : K]` (by compactness of the unit ball); the cardinality of `𝒪[K]/(ϖⁿ)`; roots of unity
of order invertible in the residue field are integral and determined by their residues; and the
action of `Gal(L/K)` on `𝒪[L]ˣ`.

## Declarations

- `mem_maximalIdeal_integer_iff`, `mem_integer_of_pow_eq_one`,
  `eq_of_pow_eq_one_of_residue_eq hm hx hy h`.
- `exists_pow_lt hϖ hγ`: some power of a uniformizer has valuation below any `γ ≠ 0`.
- `card_quotient_span_pow hπ n : |𝒪[K]/(πⁿ)| = |𝓀[K]|ⁿ`.
- `exists_basis_coord_bound`; instances `moduleFinite_integer`, `moduleFree_integer`;
  `finrank_integer : rank_{𝒪[K]} 𝒪[L] = [L : K]`.
- `integerUnitsAction K L` (the action of `Gal(L/K)` on `𝒪[L]ˣ`, used as a local instance),
  `coe_smul_integerUnits`, `integerUnitsMap_smul`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`: `exists_basis_coord_bound`, `finite_integer` (here the instance
`moduleFinite_integer`), `free_integer` (instance `moduleFree_integer`), `finrank_integer` from
`src/GroundTheory/LocalFields/Integers.lean`; `mem_integer_of_pow_eq_one`,
`eq_of_pow_eq_one_of_residue_eq` from `UnramifiedRootsOfUnity.lean`; `card_quotient_span_pow` from
`LubinTateTorsion.lean` (namespace `FormalGroup` there); `mem_maximalIdeal_integer_iff` from
`LubinTatePoints.lean`; `integerUnitsAction` (a global instance there), `coe_smul_integerUnits`,
`unitsIncl_smul` (here `integerUnitsMap_smul`) from `UnitsGalois.lean`. `exists_pow_lt` has the
statement of the source's lemma in `ExistsUnitFiltrationUnitsLeAndRangePowLe.lean` with a new proof.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The norm on `K` is the Library's `LocalGalois.localNormedField`.

## References

- J.-P. Serre, *Local Fields*, chapter II, §2, Proposition 3 (the integral closure is a discrete
  valuation ring, free of rank `[L : K]`; stated for a complete discretely valued field), p. 28.
