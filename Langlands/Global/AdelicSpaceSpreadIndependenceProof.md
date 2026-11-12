# Independence of the adelic topology of an algebraic space from its model

Author: Worker 208.

This helper module proves the spread clauses `NumberFieldSpaceSpreadStatement`
and `CurvePlaceSpaceSpreadStatement` of
`Langlands.Global.AdelicSpacePointTopologyStatement`. The source is Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (31 December 2011),
printed p.17. There a separated algebraic space `Y` of finite type over a
global field `F` gets a topology on `Y(A_F)` from a separated model of finite
type over a ring of `S`-integers, and Conrad states that this topology does not
depend on the model. The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The existence clauses come from `AdelicSpaceSpreadExistenceProof`. This module
proves the independence clauses and combines the two.

Conrad gives the independence without a detailed argument. This module
implements the standard one. First move both models to a common ring of
`S`-integers; by Worker 105's `AdelicSpaceSpreadInitialSet`, enlarging `S`
does not change the topology. Then descend the isomorphism between the generic
fibres to a morphism of models over a still larger ring of integers. That
morphism is continuous on adelic points, so one topology is finer than the
other, and symmetry gives equality.

## Declarations

Namespace `Langlands.Global.AdelicSpaceSpreadIndependenceProof`.

- `quasiCompactAtlas_of_finiteTypeOverRing`: a finite type atlas
  (`FiniteTypeOverRing`) is quasi-compact.
- `locallyOfFinitePresentation_of_finiteTypeOverRing`: over a Noetherian ring
  `C`, a finite type atlas is locally of finite presentation. The atlas
  structure map has target `Spec C`, which is locally Noetherian, so Mathlib's
  `LocallyOfFinitePresentation.iff_locallyOfFiniteType` applies.
- `compIso_hom_comp_eq`: let `g₁ = g' ≫ g`. Suppose a morphism `φ` of base
  changes along `g₁` agrees, on sections, with the base change along `g'` of a
  morphism `φi` of base changes along `g`, as in the conclusion of
  `spaceLimitMorphismDescent`. Then `φ` and `baseChangeMap g' φi` agree up to
  the iterated base change comparison `BaseChangeComparison.compIso`. The
  proof compares sections, using `mapSections_compIso_hom` and the
  `pullback_congr_left` lemmas of the base change comparison module.

The rest of the module comes in a number-field version and a function-field
version (prefixes `numberField` and `curve`). The two versions are proved the
same way; the function-field version needs `S` nonempty wherever it uses
`AdelicSpaceSpreadInitialSet.curve_spreadTopology_eq`.

- `numberField_spreadTopology_le_of_hom`, `curve_spreadTopology_le_of_hom`:
  let `X` and `Z` be models over the same `S`-integers, with `Z` separated of
  finite type. Suppose `φ : X ⟶ Z` satisfies
  `baseChangeMap φ ≫ f.hom = e.hom` on generic fibres. Then the spread
  topology defined by `(X, e)` is finer than the one defined by `(Z, f)`.
  Naturality of the generic-fibre point identification
  (`mapSections_naturality`) shows that, after the identification with the
  adelic points of `Y`, the identity map is `RingPoints.map φ`. That map is
  continuous on adelic points by Worker 105's
  `AdelicSpacePointMapsProof.numberField_continuous` and
  `AdelicSpacePointMapsProof.curve_continuous`. Both spread topologies are
  induced topologies (`continuous_iff_le_induced`).
- `numberField_exists_level_hom`, `curve_exists_level_hom`: a morphism between
  generic fibres of models `X` (separated, finite type) and `Z` (finite type)
  over the `S`-integers comes from a morphism of the level base changes to the
  `T`-integers for some `T ⊇ S`. The generic fibres are identified by
  `AdelicSpaceSpreadInitialSet.numberFieldGenericFiberIso` and
  `AdelicSpaceSpreadInitialSet.curveGenericFiberIso`. The integer rings
  containing the `S`-integers form a filtered diagram whose colimit is the
  field (`numberFieldSIntegersOverIsColimit`,
  `curvePlaceSIntegersOverIsColimit`). Its diagram of spectra is a cofiltered
  limit of affine schemes over `Spec` of the `S`-integers. The `S`-integers
  are Noetherian (`adelicSIntegersNoetherian`), so `Z` has a locally finitely
  presented atlas. `spaceLimitMorphismDescent` then gives the descended
  morphism, and `compIso_hom_comp_eq` turns its compatibility on sections into
  the stated equation.
- `numberField_spreadTopology_le`, `curve_spreadTopology_le`: for two
  separated models `X`, `Z` of finite type over the same `S`-integers, with
  identifications `e`, `f` of their generic fibres with `Y`, the topology from
  `(X, e)` is finer than the topology from `(Z, f)`. The curve version assumes
  `S` nonempty. The proof descends `e.hom ≫ f.inv` to a morphism `φT` over some
  `T ⊇ S` with the previous lemma. It rewrites both topologies as the
  topologies of the level base changes to the `T`-integers with
  `numberField_spreadTopology_eq` (respectively `curve_spreadTopology_eq`)
  from `AdelicSpaceSpreadInitialSet`, and applies `..._le_of_hom` to `φT`. The
  level base change of `Z` is separated (`IsSeparated.baseChange`) and of
  finite type (`CoordinatePointMaps.finiteTypeOverRing_baseChange`).
- `numberField_spreadTopology_independent`,
  `curve_spreadTopology_independent`: the independence clause. Models over the
  `S`-integers and the `U`-integers are both base changed to the
  `S ∪ U`-integers with the enlargement lemma of `AdelicSpaceSpreadInitialSet`.
  The two topologies there are equal by the previous lemma, applied in both
  directions with `le_antisymm`. The curve version assumes `S` and `U`
  nonempty, as `CurvePlaceSpaceSpreadStatement` does; then `S ∪ U` is
  nonempty.
- `numberFieldSpaceSpread : NumberFieldSpaceSpreadStatement`,
  `curvePlaceSpaceSpread : CurvePlaceSpaceSpreadStatement`: the spread clauses.
  Existence is `numberFieldSpaceSpreadExistence`
  (respectively `curvePlaceSpaceSpreadExistence`) from
  `AdelicSpaceSpreadExistenceProof`; independence is the previous theorem.

## Scope

The theorems cover models that are separated and of finite type, as in the
statements. The function-field version needs `k` finite and `S`, `U`
nonempty, as in `CurvePlaceSpaceSpreadStatement`. The proofs import the proof
of `spaceLimitMorphismDescent` (`SpaceLimitMorphismDescentProof`) and, through
`AdelicSpaceSpreadExistenceProof`, the proof of `spaceLimitModelExistence`.
