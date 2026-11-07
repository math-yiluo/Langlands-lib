# Uniqueness of the topology of Conrad's Proposition 5.4

Author: Worker 105.

This proof module proves the uniqueness assertion of Proposition 5.4 of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed p.15
(source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`), corrected to locally
separated spaces. It also proves the facts about schemes this needs. It builds on
`EtaleChartLocalSeparation`.

## Schemes as algebraic spaces

- `relative_diag_schemeYoneda`: for a property `P` of scheme morphisms that respects
  isomorphisms and is stable under base change, if the scheme diagonal of `U → S` has `P`
  then the diagonal of the presheaf `h_U` is representable with all represented
  projections in `P`. The proof uses the Library's `relative_diag_of_representsEqualizer`
  (`DiagonalEqualizer.lean`). For two maps `x, y : T → U` the equalizer locus is the
  pullback of the diagonal `U → U ⊗ U` along `(x, y) : T → U ⊗ U`. Its projection to `T`
  is a monomorphism and a base change of the scheme diagonal
  `pullback.diagonal U.hom`, hence in `P`. It represents the locus where `x` and `y`
  agree by the pullback property.
- `isLocallySeparated_schemeToSpace`: every scheme is a locally separated space (the
  scheme diagonal is an immersion, Mathlib).
- `isQuasiSeparated_schemeToSpace`: a scheme with quasi-separated structure morphism is a
  quasi-separated space.
- `isLocallySeparatedLocallyFiniteType_schemeToSpace`: a scheme locally of finite type
  over the field `K` is in the class of the corrected proposition. It is locally
  noetherian (Mathlib's `LocallyOfFiniteType.isLocallyNoetherian`), hence its underlying
  space is quasi-separated and so is its structure morphism. Its space is locally of
  finite type over the base by `LocallyOfFiniteTypeOverBase.of_scheme`.
- `EtaleFiniteTypeChart.isEtaleMorphism`: a chart map is étale in the Stacks sense
  (`IsEtaleMorphism`), because étale transformations compose (`IsEtale.comp`).

## Uniqueness

- `eq_etaleChartTopology_of_isAdmissible`: if a family `τ` satisfies
  `IsAdmissibleRationalPointTopology K τ`, then `τ X = etaleChartTopology K X` for every
  quasi-separated, locally separated space `X` locally of finite type. The henselian
  hypothesis is not needed. For each chart `c` of `X`, the chart scheme is in the class,
  so the scheme clause of `τ` identifies `τ` on it with the scheme point topology. The
  functoriality and étale clauses of `τ` then show that `c.pointMap` is continuous and
  open for `τ X`.
  - A `τ X`-open set has open preimage in every chart, so it is open for the étale-chart
    topology (`etaleChartTopology_isOpen_iff`).
  - An open set `O` for the étale-chart topology contains, around each of its points
    `c.pointMap y`, the `τ X`-open set `c.pointMap(c.pointMap⁻¹ O)`. Such a chart exists
    by `exists_chart_pointMap_eq` (Knutson II.6.4, as in Conrad's uniqueness argument).
    So `O` is `τ X`-open.
