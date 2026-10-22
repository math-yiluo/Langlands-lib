# Fixed-field refinement and inflation

Worker 104. This internal construction proves naturality of the published
fixed-unit cohomology isomorphism under open normal subgroup refinement.
Its generic portion works for any Galois extension `L/K`, with both fields
in an arbitrary common universe `u`, in every natural cohomological degree.

For open normal subgroups `N ≤ M`, put `F_N = L^N` and `F_M = L^M`.
`FixedFieldRefinement.fixedField_le` proves `F_M ≤ F_N`.
`fieldInclusion` is the actual intermediate-field inclusion; its ring
homomorphism defines `inclusionAlgebra`. `baseTower` and `ambientTower`
prove the scalar towers `K → F_M → F_N` and `F_M → F_N → L`.

`quotient_restriction` identifies quotient transition `Gal(L/K)/N →
Gal(L/K)/M` with restriction `Gal(F_N/K) → Gal(F_M/K)`, through
Mathlib's fixed-field quotient equivalences. Quotient induction reduces
this assertion to restriction of one automorphism of `L`; normal
restriction through the scalar tower proves it. `quotient_restriction_symm`
expresses the same identity in the inverse direction used by cohomology.

`cohomology_inflation` proves

```
finiteInflation (unitsRepresentation K L) q h ≫ fixedFieldCohomologyIso(N).hom
  = fixedFieldCohomologyIso(M).hom ≫ relativeInflation K F_M F_N q.
```

The Lean statement supplies the canonical inclusion algebra and base
scalar tower explicitly. The maps are the existing project maps.
The proof expands the published cohomology isomorphism as
`groupCohomology.mapIso`, combines the composites with `map_comp`, and
uses `map_congr` with the inverse quotient identity. The coefficient
identity follows by extensionality of linear maps, units, and subtypes:
both composites take the given invariant unit to the same ambient value.

The provenance is an internal naturality certificate for the published
`FixedFieldUnits`, `Cohomology`, and `Continuous.FiniteQuotientSystem`
interfaces and Mathlib's infinite Galois correspondence. It asserts no
vanishing, exactness, or injectivity of cohomology maps.

For a characteristic-zero field `K : Type u`, the specialization
`finiteStageFixedField_le K h` proves the requested inclusion of absolute
finite stages. `finiteStageFieldInclusion` constructs that field inclusion,
`finiteStageInclusionAlgebra` supplies its algebra structure, and
`finiteStageBaseTower` and `finiteStageAmbientTower` certify both towers.
The theorem `finiteStageRelativeIso_inflation K q h` specializes the generic
cohomology identity to the algebraic closure and states exactly

```
finiteInflation (absoluteUnitDiscreteModule K).toRep q h
    ≫ (finiteStageRelativeIso K N q).hom
  = (finiteStageRelativeIso K M q).hom
    ≫ relativeInflation K (finiteStageFixedField K M) (finiteStageFixedField K N) q.
```

For a specified finite Galois intermediate field `E` and
`h : N ≤ finiteGaloisFixingSubgroup K E`, `finiteGaloisStage_le`
proves `E ≤ finiteStageFixedField K N` using the foundation's equality
between `E` and the field fixed by its fixing subgroup. The constructions
`finiteGaloisStageFieldInclusion`, `finiteGaloisStageInclusionAlgebra`,
`finiteGaloisStageBaseTower`, and `finiteGaloisStageAmbientTower` supply
the actual inclusion and its two scalar towers.

`finiteGaloisStage_quotient_restriction` and its `_symm` form identify
quotient transition with restriction directly to `E`. Their proofs use
quotient induction and restriction through the tower, as in the generic
case. The theorem `finiteGaloisStageRelativeIso_inflation K E q h`
then states

```
finiteInflation (absoluteUnitDiscreteModule K).toRep q h
    ≫ (finiteStageRelativeIso K N q).hom
  = (finiteGaloisStageRelativeIso K E q).hom
    ≫ relativeInflation K E (finiteStageFixedField K N) q.
```

Its proof combines cohomology maps, uses the direct inverse group identity,
and proves the coefficient identity by linear-map, unit, and subtype
extensionality. Both coefficient composites retain the same closure value.
The two displayed theorems explicitly supply their inclusion algebra and
base scalar tower in their Lean types.

Worker 68 authored the published foundation `FixedFieldStages` API used
by these specializations. Worker 54 supplied the required direct-field
form. The foundation is imported by module name. The helper `closed`
used in the group formulas is definitionally the same closed subgroup
as the foundation's `finiteStageClosedSubgroup`.
