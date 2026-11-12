# Second countability of adelic levels of separated algebraic spaces

Author: Worker 105.

Helper module for the countable base in Conrad's p.17 claims
(`Langlands.Global.AdelicSpacePointTopologyStatement`). The source is Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), printed p.17. Let `X` be a separated
algebraic space of finite type over the `S`-integers. This module shows that the level and
stage topologies of `X` are second countable.

## Declarations

Namespace `Langlands.Global.AdelicSpaceLevelSecondCountable`.

- `secondCountableTopology_fieldValued`: let `L` be a henselian valued field with a countable
  base and a countable Galois family, and `X` separated of finite type. Then
  `fieldValuedPointTopology` along any map to `L` is second countable. It is induced from the
  étale-chart topology of the base change, which is second countable by
  `EtaleChartSecondCountable.secondCountableTopology_etaleChartTopology`.
- `infinite_hasCountableGaloisFamily`: an archimedean completion of a number field has a
  countable Galois family. It is isomorphic to `ℝ` or `ℂ`
  (`ringEquivRealOfIsReal`, `ringEquivComplexOfIsComplex`), so its irreducible polynomials have
  degree at most two.
- `numberField_factor`, `curve_factor`: every factor of a level is second countable. Each case
  needs a countable base and a countable Galois family for the completion:
  - archimedean completions: second countable by `infiniteCompletion_secondCountableTopology`;
    Galois family by `infinite_hasCountableGaloisFamily`;
  - non-archimedean completions: second countable by `finiteCompletion_secondCountableTopology`
    and `curvePlaceCompletion_secondCountableTopology`; Galois family by
    `hasCountableGaloisFamily_of_isUltrametricDist`, from completeness, the ultrametric norm and
    separability.
- `numberField_level`, `curve_level`: **levels are second countable**. The level topology is
  induced from a product of factors over a countable index type (`finitePlace_countable`,
  `curvePlace_countable`).
- `numberField_stage`, `curve_stage`: **stages are second countable**. Each is induced from the
  level of the base change to the `T`-integers.
