# Uniqueness of the structure of a finite extension of a local field

`Langlands/GaloisCohomology/Local/Arithmetic/Uniqueness.lean`, namespace `Langlands.GaloisCohomology.Local`.

For a finite extension `L/K` of nonarchimedean local fields, the topology of `L` is the module
topology over `K`, every `K`-algebra map between finite extensions is continuous, a closed
embedding and preserves the valuative relation, and the valuative relation and topology of `L`
are determined by those of `K`. In particular `Gal(L/K)` preserves the valuation and acts on the
ring of integers and on the residue field.

## Declarations

- `t2Space_of_isNonarchimedeanLocalField`, `nontriviallyNormedField K` (the norm of the rank-one
  valuation), `completeSpace_nontriviallyNormedField`, `isModuleTopology`.
- `vle_iff_not_valuation_div_lt_one`, `vle_map_iff_of_valuation_lt_one_iff`,
  `tendsto_pow_atTop_nhds_zero_iff`: `xⁿ → 0` iff `v(x) < 1`.
- For `f : L →ₐ[K] M`: `continuous_algHom`, `isClosedEmbedding_algHom`, `valuation_map_lt_one_iff`,
  `vle_map_iff`, `vlt_map_iff`, `valuativeExtension_algHom`, `valuation_map_le_iff`,
  `valuation_map_lt_iff`, `valuation_map_eq_iff`, `map_mem_integer_iff`; `continuousAlgHom f`;
  `integerAlgHom f : 𝒪[L] →ₐ[𝒪[K]] 𝒪[M]` (`isLocalHom_integerAlgHom`); `residueAlgHom f`.
- `valuativeExtension_of_isScalarTower`; `topologicalSpace_eq_moduleTopology`,
  `topologicalSpace_unique`, `valuativeRel_unique`: the structures of a finite extension are unique.
- `valuation_algEquiv_apply K L σ x : v(σ x) = v(x)`; `vle_algEquiv_iff`; `continuousAlgEquiv`,
  `homeomorph`; `integerAlgEquiv K L : Gal(L/K) →* Aut(𝒪[L])`; `residueAlgEquiv K L :
  Gal(L/K) →* Aut(𝓀[L]/𝓀[K])` with `residueAlgEquiv_residue`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/LocalFields/Uniqueness.lean`, with the names unchanged.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J.-P. Serre, *Local Fields*, chapter II, §2, Proposition 3, p. 28, and chapter I, §7 (the action
  of the Galois group on the valuation ring and the residue field), pp. 20–22.
