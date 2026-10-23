# Proof of the idele-class cohomology tower identities

The theorem `Langlands.ClassField.Global.ideleClassCohomologyTowerLaws.{u}`
proves the published proposition
`Langlands.ClassField.Global.IdeleClassCohomologyTowerLaws.{u}` from
`CohomologyTowerStatement`. It establishes restriction transitivity,
inflation transitivity, and the commuting inflation–restriction square for
the actual idele-class cohomology maps, in every natural degree, including
zero. It retains the statement's compatible number-field towers in a common
universe and its Galois hypotheses.

The proof first establishes four arithmetic identities in the namespace
`Langlands.Global.AdelicFunctoriality`:

- `finitePlace_under_under` reduces equality of the finite places below a
  place in a tower to transitivity of ideal contraction, `Ideal.under_under`.
  This auxiliary lemma does not need the section's number-field assumptions.
- `finiteAdeleInclusion_trans` proves equality at each finite coordinate.
  The coordinate indices agree by the preceding lemma. The two continuous
  maps between completions agree on the embedded ground field by the
  scalar-tower law for algebra maps. The existing
  `adicCompletion_coordinate_eq` then gives equality on every coordinate
  by density, including the required transport between the equal place indices.
- `adeleInclusion_trans` combines that finite-coordinate identity with
  `infiniteAdeleMap_comp` and the scalar-tower identity for algebra maps.
- `ideleClassInclusion_trans` chooses an idele representative of the
  quotient class, applies the adele identity to its underlying unit, and
  descends the resulting equality to the idele-class quotient.

Each cohomology identity is then proved as an equality of morphisms before
evaluating it on a class. Expanding the actual restriction and inflation
maps, `groupCohomology.map_comp` rewrites their composites and
`groupCohomology.map_congr` compares the group and coefficient maps.

For `ideleClassRestrictionTransitivity`, the scalar restrictions of
automorphisms agree by extensionality and both coefficient maps are the
identity. For `ideleClassInflationTransitivity`, the group maps agree by
`IsScalarTower.AlgEquiv.restrictNormalHom_comp` and the coefficient maps
agree by `ideleClassInclusion_trans`, passed through the additive wrapper.
For `ideleClassInflationRestrictionCompatibility`, the Galois structure
over the intermediate base is derived using
`IsGalois.tower_top_of_isGalois`. The two group maps agree after applying
the injective algebra map to the larger field, using
`AlgEquiv.restrictNormal_commutes`; the coefficient maps agree directly.
The final theorem assembles these three results as a conjunction.

This is a formal functoriality proof of the derived statement whose
provenance is documented in `CohomologyTowerStatement.md`. It introduces no
additional arithmetic assumption. The identities alone do not establish
inflation injectivity, cohomological vanishing, or existence of a global
invariant map.
