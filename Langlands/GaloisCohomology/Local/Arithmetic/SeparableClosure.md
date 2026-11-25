# Valuations on algebraic extensions and their intermediate fields

`Langlands/GaloisCohomology/Local/Arithmetic/SeparableClosure.lean`, namespaces `Langlands.GaloisCohomology.Local` and `Langlands.GaloisCohomology.Local.IntermediateFieldStructure` (scoped instances).

For a nonarchimedean local field `K` and an algebraic extension `Ω` (for instance a separable
closure), every valuative relation on `Ω` extending that of `K` compares elements by Mathlib's
spectral norm (`vle_iff_spectralNorm_le`); hence it is unique and invariant under `Ω ≃ₐ[K] Ω`. The
spectral norm itself supplies such a relation and a topology (`algebraicValuativeRel`,
`algebraicTopology`). An intermediate field carries the restricted relation (scoped instances,
activated by `open … IntermediateFieldStructure`), and a finite intermediate field of an algebraic
extension with valuative topology is a nonarchimedean local field, its structure being the
Library's spectral structure `LocalField.FiniteExtension`. The local Euler characteristic uses this
to treat the fixed fields of open subgroups of `Gal(Ksep/K)` as local fields.

## Declarations

- `valuation_le_one_of_aeval_eq_zero`: roots of monic integral polynomials are integral.
- `algebraicNormedField K L` (the spectral norm for the Library's norm on `K`),
  `algebraicNormedField_isUltrametricDist`, `algebraicNormedField_norm_algebraMap`,
  `localNormedField_le_iff_vle`.
- `valuation_le_one_of_spectralNorm_le_one`, `valuation_lt_one_iff_spectralNorm_lt_one`,
  `vle_iff_spectralNorm_le`, `valuativeRel_eq_of_isAlgebraic` (uniqueness),
  `valuation_algEquiv_apply_of_isAlgebraic`.
- `algebraicValuativeRel K L`, `algebraicTopology K L`, `algebraicValuativeRel_vle_iff`,
  `algebraicValuativeRel_valuativeExtension`, `algebraicTopology_isValuativeTopology`.
- Scoped instances `intermediateField_valuativeRel`, `intermediateField_valuativeExtension_right`,
  `intermediateField_valuativeExtension_left`, `intermediateField_isNonarchimedeanLocalField_of_finiteDimensional`;
  `intermediateField_coe_vle_coe_iff`, `intermediateField_valuation_coe`,
  `valuativeExtension_inclusion`.
- `topologicalSpace_eq_of_isValuativeTopology`, `exists_algebraMap_valuation_lt`,
  `intermediateField_isValuativeTopology` (the subspace topology is valuative).
- `spectral_valuativeExtension`, `valuativeRel_eq_spectral` (a relation extending `K`'s on a finite
  extension is the Library's spectral one), `intermediateField_isNonarchimedeanLocalField`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/LocalFields/SeparableClosure.lean` (sections Integral,
Spectral, Existence, Topology, Inclusion, Finite) and `IntermediateField.lean` (section Algebraic).
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Changes: the norm on `K` is the Library's `LocalGalois.localNormedField` in place of the source's
`normedField`; the finite-extension structure is the Library's `LocalField.FiniteExtension`
(`normedField`, `valuativeRel`, `isLocalField`) in place of the source's `finiteExtensionStructure`
(`valuativeRel_eq_finiteExtensionStructure` becomes `valuativeRel_eq_spectral`). The source's global
instances on intermediate fields are scoped here; `IntermediateField.coe_vle_coe_iff`,
`IntermediateField.valuation_coe`, `IntermediateField.valuativeExtension_inclusion` are renamed
`intermediateField_coe_vle_coe_iff`, `intermediateField_valuation_coe`,
`valuativeExtension_inclusion`. The source's instances on `SeparableClosure K` and its
`homeomorphOfIsAlgebraic` are not taken.

## References

- J.-P. Serre, *Local Fields*, chapter II, §2, Proposition 3 and its corollaries (unique extension
  of the valuation to a finite extension of a complete field), pp. 28–29.
