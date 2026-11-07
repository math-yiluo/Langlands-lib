# Towers over levels satisfying a property that holds at every level

This internal construction handles the special case of the published
`Langlands.Shimura.RestrictedLevelTowerCohomology` in which the property `P`
of levels holds at every compact open level. A tower of schemes over the
levels satisfying `P` is then a tower over all levels, and its colimit
cohomology over the levels satisfying `P` is the published colimit
cohomology over all levels (`Langlands.Shimura.LevelTowerCohomology`). All
declarations are in namespace
`Langlands.Shimura.RestrictedLevelTowerCohomology`.

## Motivation and scope

A tower that is a priori defined only at sufficiently small levels can turn
out to be defined at every level of a smaller group. For example, the levels
`e⁻¹ (K₀ × K')` of a split group are all sufficiently small once the fixed
factor `K₀` is (see `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`,
submitted together with this module). This module transfers such a tower to
the published framework of towers over all levels. It constructs no
schemes, coefficients or specific property of levels.

## Inputs

Let `G : Type u` be a group with a topology, let
`P : ObjectProperty (CompactOpenLevel G)`, and let
`hP : ∀ K : CompactOpenLevel G, P K`. The published
`RestrictedLevelTowerCohomology` provides, for a tower
`T : P.FullSubcategory ⥤ Scheme.{u}` with étale level maps and a commutative
ring `R`, the coefficient diagrams `CoefficientDiagram R T.op`,
`IsLevelTrivialCoefficients`, `restrictCoefficients`, `colimitCohomology`,
`smoothColimitCohomology`, `smoothColimitSections` and the isomorphisms
`colimitCohomologyRestrictIso`, `ι_colimitCohomologyRestrictIso_hom`,
`smoothColimitCohomologyRestrictIso` and `smoothColimitSectionsRestrictIso`
for coefficients restricted from a tower over all levels. The published
`RestrictedLevelColimit` provides the predicates `IsDownwardClosed` and
`IsConjStable` and the colimit legs `RestrictedLevelColimit.ι`. The
published `Geometry.EtaleCohomologyReindex` provides
`CoefficientDiagram.reindex`.

## Levels

- `extendLevels hP : CompactOpenLevel G ⥤ P.FullSubcategory` is
  `P.lift (𝟭 _) hP`, every level regarded as a level satisfying `P`.
- `isDownwardClosed_of_forall hP : IsDownwardClosed P` and, for a
  topological group `G`, `isConjStable_of_forall hP : IsConjStable P`.

## Towers and coefficients

Let `T : P.FullSubcategory ⥤ Scheme.{u}`.

- `extendTower hP T` is `extendLevels hP ⋙ T`, the tower over all levels.
- `restrict_extendTower hP T : P.ι ⋙ extendTower hP T = T`, by `rfl`.

Assume moreover that every level map of `T` is étale, and let `R : Type u`
be a commutative ring.

- The instance `etale_extendTower_map` states that every level map of
  `extendTower hP T` is étale.
- `extendCoefficients hP D` is `CoefficientDiagram.reindex (extendLevels hP).op D`,
  the coefficients `D` on `T` as coefficients on `extendTower hP T`.
  `extendCoefficients_obj` states that its value at `K` is
  `D.obj (op ⟨K.unop, hP K.unop⟩)`, and `extendCoefficients_cohomology`
  states that its degree `q` cohomology presheaf is
  `(extendLevels hP).op ⋙ D.cohomology q`; both hold by `rfl`.
- `restrictCoefficients_extendCoefficients hP D`: restricting the extended
  coefficients to the levels satisfying `P` gives back `D`, by `rfl`.
- `isLevelTrivialCoefficients_extend hP hD`: if `D` is level-trivial, so is
  its extension, in the sense of `LevelTowerCohomology.IsLevelTrivialCoefficients`.

## Colimit cohomology

Assume moreover that `G` is a topological group, that `P` is conjugation
stable and that some compact open level of `G` exists.

- `colimitCohomologyExtendIso hP D q` is an isomorphism of objects with an
  action of `G` from `colimitCohomology D q` (over the levels satisfying
  `P`) to `LevelTowerCohomology.colimitCohomology (extendCoefficients hP D) q`
  (over all levels).
- `ι_colimitCohomologyExtendIso_hom hP D q K`: on the classes of level `K`,
  the forward map of this isomorphism is the colimit leg at the level
  `K.obj` of `LevelColimit.ι` for the extended coefficients.
- `smoothColimitCohomologyExtendIso hP D hD q` and
  `smoothColimitSectionsExtendIso hP D hD` are the corresponding isomorphisms
  of smooth representations of `G` for level-trivial coefficients `D`, for
  cohomology in degree `q` and for global sections.

## Proof outline

Since `restrictCoefficients (extendCoefficients hP D)` is `D` by `rfl`, each
isomorphism is the published restriction isomorphism
(`colimitCohomologyRestrictIso`, `ι_colimitCohomologyRestrictIso_hom`,
`smoothColimitCohomologyRestrictIso` or `smoothColimitSectionsRestrictIso`)
applied to `extendCoefficients hP D`. The instances it needs are
`isDownwardClosed_of_forall hP` and the nonemptiness of `P.FullSubcategory`,
witnessed by an arbitrary level.

## Provenance

This is an internal construction from the published
`RestrictedLevelTowerCohomology`, `LevelTowerCohomology`,
`RestrictedLevelColimit` and `Geometry.EtaleCohomologyReindex`. It is not
taken from a source and formalizes no published statement.
