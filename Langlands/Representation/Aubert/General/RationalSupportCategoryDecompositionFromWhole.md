# The actual rational support decomposition from the whole-category splitting

Worker 4195. This module reduces the exact Library proposition
`Langlands.Aubert.General.RationalPointFamily.RationalSupportCategoryDecompositionStatement.{u, v}`
(Renard, Théorème VI.7.2, grouped by association classes of standard Levis) to
one published proposition that is not yet proved: the first decomposition of
Renard VI.3.5,
`Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`.
It therefore does not prove the support decomposition. It is an internal step
of proof task `8452c8a4-3686-47c2-80cf-c4ff4e16b3b2`. No source states this
implication as a separate result.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
Théorème VI.7.2 and its proof, printed pp. 182–185 / PDF pp. 188–191; VI.3.5,
printed pp. 146–147 / PDF pp. 152–153. In the source, the proof of VI.7.2 uses
the cuspidal part of the Jacquet modules (from VI.3.5 applied to the Levis),
the support of induced cuspidal objects and the uniqueness of cuspidal data
(VI.5.4). The published reductions below make each of these steps depend on
VI.3.5 alone.

## Declarations

- `rationalSupportCategoryDecomposition_of_wholeStatement`: the VI.3.5
  whole-category statement at universes `u, max (u + 1) v` implies
  `RationalSupportCategoryDecompositionStatement.{u, v}`.
- `rationalSupportCategoryDecompositionOfWholeStatement`: the same theorem as a
  `def` whose type is the implication between the two published propositions
  (the `linter.defProp` warning is disabled only for this declaration).

The field and group universe `u` and the representation universe `v` stay
independent. Both propositions are used exactly as published; this module
changes neither.

## The proof

The proof is a term. It applies the published
`rationalSupportCategoryDecomposition_of_inducedCuspidal.{u, v}` (module
`RationalSupportCategoryDecompositionReduction`) to three arguments, each
obtained from the single hypothesis `hwhole`:

1. `hEmb : RationalCuspidalInducedEmbeddingStatement.{u, max (u + 1) v}` is the
   published `rationalCuspidalInducedEmbedding_of_wholeStatement` (module
   `CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole`), instantiated at
   universes `u, max (u + 1) v`, where it needs VI.3.5 at exactly
   `u, max (u + 1) v`.
2. `hInd : RationalInducedCuspidalSupportCategoryStatement.{u, v}` is the
   published `rationalInducedCuspidalSupportCategory_of_wholeStatement` (module
   `InducedCuspidalSupportCategoryReduction`), which needs VI.3.5 at
   `u, max (u + 1) v`.
3. `hAssoc : RationalCuspidalSupportAssociationStatement.{u, v}` is obtained in
   three published steps: `rationalCuspidalExtractionInputs_of_wholeStatement`
   (module `RationalLeviInductionExclusionFromWhole`, VI.3.5 at
   `u, max (u + 1) v`) gives the geometric-filtration and proper-standard
   exclusion inputs; `rationalCuspidalJacquetFactorExtraction_of_inputs`
   (module `RationalCuspidalExtractionInputs`) turns them into
   `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`; and
   `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`
   (module `RationalCuspidalSupportAssociationReduction`) gives the
   association statement.

The binders of all statements are the same structural telescope as the
target, so no transport is needed. `lean_check` reports zero errors and
warnings and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Dependencies and scope

The only hypothesis is VI.3.5 at universes `u, max (u + 1) v`; its proof is
task `4bee987a-093b-4054-bd65-7360168351d2`. No finite-length, admissibility,
finite-generation, exactness, compactness, endpoint or compact-limit premise
is added. The transitive dependencies are those of the published reductions
named above: Frobenius reciprocity and the actual geometric filtration of
`r_J i_I` (through the embedding, induced-support and extraction reductions),
and the proved association invariance used inside
`rationalSupportCategoryDecomposition_of_inducedCuspidal`. No Langlands
classification or character independence is used. Once VI.3.5 is proved, the
target is the direct application
`rationalSupportCategoryDecomposition_of_wholeStatement hwhole`.
