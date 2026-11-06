# Colimit cohomology of towers over levels satisfying a property

This internal construction repeats the published smooth colimit cohomology
of level towers (`Langlands.Shimura.LevelTowerCohomology`) for towers of
schemes defined only on the compact open levels satisfying a property `P`.
It uses the restricted colimits of `Langlands.Shimura.RestrictedLevelColimit`.
For a tower over all levels, it restricts coefficients to the levels
satisfying `P` and identifies the resulting smooth colimit cohomology with the
published one over all levels, naturally in the coefficients. All
declarations are in namespace
`Langlands.Shimura.RestrictedLevelTowerCohomology`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, forms the cohomology of the tower of Shimura varieties with its action
of finite adelic groups: after (3.5) on printed p. 307 for the prime-to-ℓ
finite adeles, and in Proposition 4.10 on printed p. 311 for `GG(A_f^{ℓ,p})`
as `K(N)^{ℓ,p}` varies. Moduli schemes for Shimura varieties are often
constructed only for sufficiently small levels, and such a tower is then a
functor on a full subcategory of levels. This module forms the colimit cohomology of such a
tower. It constructs no Shimura varieties, Harris coefficient systems or
specific property of levels; these are inputs. It gives no Galois action,
Hecke-algebra action, finiteness, compact support or comparison with a limit
scheme. Harris's passages are motivation only; no statement from them is
formalized.

## Inputs

Let `G : Type u` be a group with a topology and
`P : ObjectProperty (CompactOpenLevel G)`. Let
`T : P.FullSubcategory ⥤ Scheme.{u}` have `Etale (T.map a)` for every arrow
`a` between levels satisfying `P`; the instance `etale_op_map` supplies
étaleness for `T.op`. Let `R : Type u` be a commutative ring. The coefficients
are the published compatible coefficient diagrams `CoefficientDiagram R T.op`:
module sheaves `D.obj (op K)` on the small étale site of `T K` with maps
`D.map a : f_a^*(D.obj (op L)) ⟶ D.obj (op K)`, where `f_a = T.map a.unop`.
The published `D.cohomology q` and `D.sections` are functors
`P.FullSubcategoryᵒᵖ ⥤ ModuleCat R`.

## Level triviality

- `IsLevelTrivialCoefficients D` states, for every level `K` satisfying `P`
  and every `k ∈ K`, that the scheme morphism of
  `restrictedSelfArrow P K k hk` equals that of the identity arrow, and that
  the coefficient map of the self-arrow is the identity coefficient map
  transported along this equality by the published `restrictionCongr`.
  `levelTrivialCoefficients T R` is this as a property of coefficient
  diagrams.
- `isLevelTrivial_cohomology` and `isLevelTrivial_sections` state that, under
  this condition, `D.cohomology q` and `D.sections` satisfy
  `RestrictedLevelColimit.IsLevelTrivial`. The proofs are those of the
  published `LevelTowerCohomology` lemmas: rewrite the coefficient map, apply
  `cohomologyMap_congr`, and use the degree-zero identification for sections.

## Restriction of towers over all levels

Let `T₀ : CompactOpenLevel G ⥤ Scheme.{u}` have étale maps along all level
arrows. The instance `etale_restrict_map` states that `P.ι ⋙ T₀` has étale
maps.

- `restrictCoefficients D₀` is the published
  `CoefficientDiagram.reindex P.ι.op D₀`, a coefficient diagram on
  `(P.ι ⋙ T₀).op`. `restrictCoefficients_obj`,
  `restrictCoefficients_cohomology` and `restrictCoefficients_sections` state,
  by `rfl`, that its objects, cohomology and sections are those of `D₀`
  restricted along `P.ι.op`.
- `isLevelTrivialCoefficients_restrict` states that restriction preserves
  level triviality (published `LevelTowerCohomology.IsLevelTrivialCoefficients`
  to the restricted condition), and `restrictCoefficientsFunctor P R T₀` is
  restriction as a functor between the full subcategories of level-trivial
  coefficient diagrams, lifted from the published `reindexFunctor`.

## Colimit representations

Assume that `G` is a topological group and `IsConjStable P`.

- `colimitCohomology D q` is `RestrictedLevelColimit.action (D.cohomology q)`;
  it needs no level triviality.
- `smoothColimitCohomology D hD q` and `smoothColimitSections D hD` are
  `RestrictedLevelColimit.smoothRep` for cohomology and for sections.
- `smoothColimitCohomologyFunctor T R q` is the functor from level-trivial
  coefficient diagrams to `SmoothRep R G`, composed of the published
  coefficient-diagram cohomology functor, the lift into level-trivial
  presheaves and `RestrictedLevelColimit.smoothFunctor P R`.
- `smoothColimitCohomology_ρ_ι_apply` states that `g` sends the image of a
  class `x` of level `K` to the image at level `restrictedConj P g K` of
  `cohomologyMapWithCoefficients (T.map (restrictedConjArrow P g K)) R q
  (D.map (restrictedConjArrow P g K).op)` applied to `x`.
- `exists_level_class` states, assuming `IsDownwardClosed P` and
  `Nonempty P.FullSubcategory` instead of conjugation stability, that every
  colimit class comes from a single level satisfying `P`.

## Comparison with towers over all levels

Assume that `G` is a topological group, `IsConjStable P`,
`IsDownwardClosed P` and `Nonempty P.FullSubcategory`, and let `T₀` be as
above.

- `colimitCohomologyRestrictIso D₀ q` identifies
  `colimitCohomology (restrictCoefficients D₀) q` with the published
  `LevelTowerCohomology.colimitCohomology D₀ q` in `Action (ModuleCat R) G`.
  It is `RestrictedLevelColimit.actionRestrictIso (D₀.cohomology q)`.
  `ι_colimitCohomologyRestrictIso_hom` states that it matches the colimit
  inclusion of level `K` with `LevelColimit.ι (D₀.cohomology q) K.obj`.
- For level-trivial `D₀`, `smoothColimitCohomologyRestrictIso D₀ hD₀ q` and
  `smoothColimitSectionsRestrictIso D₀ hD₀` identify the restricted smooth
  colimit cohomology and sections with the published
  `LevelTowerCohomology.smoothColimitCohomology D₀ hD₀ q` and
  `LevelTowerCohomology.smoothColimitSections D₀ hD₀`.
- `smoothColimitCohomologyFunctorRestrictIso P R T₀ q` is the natural
  isomorphism between `restrictCoefficientsFunctor P R T₀` followed by
  `smoothColimitCohomologyFunctor (P.ι ⋙ T₀) R q` and the published
  `LevelTowerCohomology.smoothColimitCohomologyFunctor T₀ R q`. Naturality is
  `RestrictedLevelColimit.map_colimitRestrictIso_hom` for the induced map of
  cohomology diagrams.

## Provenance

This is an internal assembly of the published `CoefficientDiagram`
cohomology over varying schemes, its reindexing along index functors,
`restrictionCongr` and `cohomologyMap_congr`, the published
`LevelTowerCohomology` constructions, and the restricted colimits of
`Langlands.Shimura.RestrictedLevelColimit`. Harris's passages are cited only
as motivation.
