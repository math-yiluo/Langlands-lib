# Completion from open finite quotients

Worker 21 authors this construction pair for the local class-field construction
task. It supplies actual objects and maps; it does not supply reciprocity.

For a topological group `G`, `ContinuousProfinite.OpenFiniteQuotient G` is the
subtype of Mathlib's finite-index normal subgroups whose carriers are open.
Each `Quotient` is the actual group quotient with its quotient topology.
Openness proves this topology discrete; finite index proves the quotient finite.

`QuotientProduct` is their product with its product topology. `diagonal` is the
continuous family of quotient maps. `imageClosure`, also exposed as the type
`Completion`, is the topological closure of its image subgroup. It inherits
its topology from the product. The compactness, Hausdorffness and total
disconnectedness certificates make `profiniteGroup` an actual `ProfiniteGrp`.
The map `eta` uses the original topology on `G` and has dense range by the
definition of this closure. No injectivity of `eta` is asserted.

The intrinsic `projection` maps to the actual finite quotients are continuous.
Pullback of open finite-index normal subgroups along a continuous homomorphism
gives `OpenFiniteQuotient.comap`; `quotientMap` is the usual quotient-group map.
These coordinates give `productMap`. Continuity carries the closure of the
diagonal image into the corresponding closure in the target, supplying the
intrinsic certificate for `map` on completions. This construction adds no
properness, surjectivity or injectivity assumptions on the original homomorphism.

`LocalMultiplicative.profiniteCompletion T` specializes this construction to the
actual units of a finite extension of `Q_p` and its specified `TopologicalData`.
`completionMap T` is continuous and `completionMap_dense` gives density. The
profinite object is distinct from the generally noncompact group of field units.
It is not identified here with the absolute-Galois abelianization, nor with a
topological Weil abelianization.

## Source and audit

This is a derived construction of the topological finite-quotient completion
needed for the formulation in Serre, *Local Fields*, English translation
(1979), Chapter XI, sections 4–5, printed pages 173–175 / PDF pages 179–181.
Registered source: `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `C:/Central-Library/Serre--Local Fields--1979.pdf`.
Worker 21 read those original passages. Serre describes a completion for the
norm-group topology and then relates norm groups to open finite-index groups
through an existence theorem. This module does not assume that theorem and
does not equate its index set with the norm groups. It constructs the completion
using open finite quotients directly. The closure model is an implementation
of that completion; no comparison with another model or universal-property
equivalence is claimed as a proved result in this pair.

Pinned Mathlib already supplies `FiniteIndexNormalSubgroup`,
`QuotientGroup`, `Subgroup.topologicalClosure`, product/subtype topologies and
`ProfiniteGrp`. Its `ProfiniteGrp.ProfiniteCompletion` construction indexes
all finite quotients of an underlying group with no supplied source topology.
This module retains openness explicitly, avoiding an unproved continuity
assertion for that other canonical map.

The sole project import is `Langlands.LocalField.Definitions`, artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1. The prepared environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Native compilation of this pair succeeded without diagnostics. Development
compilation is not mathematical acceptance. Exact declaration validation,
independent semantic review and current Library publication remain required.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.Completion` to
`Langlands.ClassFieldTheory.Local.Completion` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.


## Topic-hierarchy migration ledger

This is an internal, meaning-preserving Library organization change by Worker 63
for task `295b0f1c-439f-4b3e-8c86-14e5bd541262`, based on Library commit
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 authored the
seven construction pairs. Of the seven affected Library importers, Worker 10
authored UnitNormStatement and ProfiniteReciprocityStatement, Worker 21
authored ReciprocityRelations, Workers 21 and 53 authored
ResidueNormalization, Worker 42 authored TateNormQuotient, Worker 68
authored the absolute upper ramification module Herbrand.Absolute, and Worker 28
authored the cyclic norm quotient CyclicNorm. Worker 21 also
authored ReciprocitySystem, whose Markdown describes the imports of
ReciprocityRelations.
The original source correspondence above and in each canonical pair is retained.
This migration contributes no local class-field theorem or new mathematical assumption.

### Module map

Each old module remains as a one-import, declaration-free re-export. Its paired
Markdown directs readers to the canonical documentation. Mathematical declaration
names do not follow the module move: all listed names are intentionally retained.

| Old module | Canonical module |
| --- | --- |
| `Langlands.LocalClassField.Completion` | `Langlands.ClassFieldTheory.Local.Completion` |
| `Langlands.LocalClassField.FiniteArtin` | `Langlands.ClassFieldTheory.Local.FiniteArtin` |
| `Langlands.LocalClassField.Galois` | `Langlands.ClassFieldTheory.Local.Galois` |
| `Langlands.LocalClassField.Norms` | `Langlands.ClassFieldTheory.Local.Norms` |
| `Langlands.LocalClassField.Transfer` | `Langlands.ClassFieldTheory.Local.Transfer` |
| `Langlands.LocalClassField.Units` | `Langlands.ClassFieldTheory.Local.Units` |
| `Langlands.LocalClassField.WeilAbelianization` | `Langlands.ClassFieldTheory.Local.WeilAbelianization` |


At the pinned base, seven Library modules imported an old path. They stay at
their existing paths, and only those import lines change:

| Importer | Imports moved to the canonical path |
| --- | --- |
| `Langlands.ClassFieldTheory.Local.UnitNormStatement` | Units, Norms |
| `Langlands.ClassFieldTheory.Local.ReciprocityRelations` | Units, Completion, FiniteArtin, WeilAbelianization, Transfer |
| `Langlands.ClassFieldTheory.Local.ResidueNormalization` | Units |
| `Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement` | Completion, FiniteArtin |
| `Langlands.ClassFieldTheory.Local.TateNormQuotient` | Norms |
| `Langlands.LocalFactor.Ramification.Herbrand.Absolute` | Galois |
| `Langlands.ClassFieldTheory.Local.CyclicNorm` | Norms |

ReciprocityRelations.md had one paragraph naming the old directory. That paragraph
and the sentence about its development check now describe the canonical imports.
ProfiniteReciprocityStatement.md named old module paths in two passages: the
Transfer companion sentence and the paragraph listing its imported modules. Both
now give the canonical module and the former path, and its development-check
sentence records that the check used the original imports.
TateNormQuotient.md named the Norms module in one sentence, which now gives the
canonical module and the former path. Herbrand/Absolute.md likewise named the
Galois module in one sentence, which now gives the canonical module and the
former path; its reference to the declaration
`Langlands.LocalClassField.localAbelianGaloisProjection` keeps that unchanged
name. ReciprocitySystem imports neither an old nor a canonical moved path, and
its Lean source is unchanged. One sentence of
ReciprocitySystem.md said that ReciprocityRelations imports the pairs under
`Langlands/LocalClassField`; it now names `Langlands/ClassFieldTheory/Local`
and the former directory. ResidueNormalization.md and CyclicNorm.md name no old
module path and are unchanged; CyclicNorm.md's reference to the declaration
`Langlands.LocalClassField.NormQuotient` keeps that unchanged name. Existing local CFT statements, Cohomology and all other Library
Lean sources retain their original bytes.

### Integration against the current Library

Integrator completed the import migration against Library commit
`c4076e8f9e0c741ca14fc16ba1cd82671b9de609`. Five additional importers had
arrived since the pinned migration base. Their declaration text is unchanged;
only the imports below and corresponding module references in their paired
Markdown are updated. The seven compatibility re-exports remain available.

| Additional importer | Import moved to the canonical path |
| --- | --- |
| `Langlands.LocalClassField.AbelianizationTransport` | Galois |
| `Langlands.Weil.Local.AssemblyProof` | Galois |
| `Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyStatement` | Units |
| `Langlands.ClassFieldTheory.Local.UpperReciprocityStatement` | Units |
| `Langlands.ClassFieldTheory.Local.FiniteConductorStatement` | Units |

The seven relocated construction sources retain the current Library's exact
non-import text. Declaration names, namespaces, bodies, and statement types
remain as recorded below. Public-note navigation updates are a separate notes
contribution; existing links still resolve through the compatibility pages.

### Declaration-name map

Every public name below maps to itself. Lists include named source declarations;
the compiled-declaration comparison also covers the anonymous generated instance,
equation lemmas and other compiler-generated declarations. All universes, binder
information, instance arguments, complete types and values are compared.

#### Completion

- `Langlands.LocalClassField.ContinuousProfinite.OpenFiniteQuotient` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.OpenFiniteQuotient.Quotient` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.OpenFiniteQuotient.quotientDiscrete` (instance): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.OpenFiniteQuotient.projection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.OpenFiniteQuotient.comap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.OpenFiniteQuotient.quotientMap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.QuotientProduct` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.diagonal` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.imageClosure` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.Completion` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.completionCompact` (instance): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.profiniteGroup` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.eta` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.eta_dense` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.projection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.productMap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ContinuousProfinite.map` (def): same public name and complete declaration.
- `Langlands.LocalClassField.LocalMultiplicative.profiniteCompletion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.LocalMultiplicative.completionMap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.LocalMultiplicative.completionMap_dense` (theorem): same public name and complete declaration.

Private source helpers, whose source text is retained:

- `Langlands.LocalClassField.ContinuousProfinite.productMap_mem_closure` (theorem).

The original elaborated module contains 52 declarations, including generated helpers.

#### FiniteArtin

- `Langlands.LocalClassField.FiniteArtinFamily` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteNormResidueRelation` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteArtinRestrictionRelation` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteArtinSystemRelation` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteFamilyOfHom` (def): same public name and complete declaration.
- `Langlands.LocalClassField.ProfiniteNormResidueRelation` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteNormQuotientMap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteNormResidueEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.NormTrivialCharacter` (def): same public name and complete declaration.
- `Langlands.LocalClassField.normQuotientCharacterEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.characterTransport` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteArtinCharacterEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteTransfer` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteAbelianTransfer` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteFixingGroupEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteGaloisInclusion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteGaloisAbelianInclusion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.finiteGaloisAbelianTransfer` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteNormCompatibility` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteTransferCompatibility` (def): same public name and complete declaration.

The original elaborated module contains 67 declarations, including generated helpers.

#### Galois

- `Langlands.LocalClassField.abelianizationHausdorff` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.abelianizationProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.abelianizationLift` (def): same public name and complete declaration.
- `Langlands.LocalClassField.abelianizationLiftEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.abelianizationMap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.quotientNonarchimedean` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.field` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.galoisGroup` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.finiteGroup` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.fixingOpenSubgroup` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.restriction` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.abelianRestriction` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.restrictionOfLE` (def): same public name and complete declaration.
- `Langlands.LocalClassField.FiniteAbelianExtension.asPadicField` (def): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteAbelianizationProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteGaloisNonarchimedean` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteAbelianizationProfinite` (def): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteAbelianizationMap` (def): same public name and complete declaration.
- `Langlands.LocalClassField.LocalFiniteAbelianExtension` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.localAbelianGaloisGroup` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localAbelianGaloisProjection` (def): same public name and complete declaration.

Private source helpers, whose source text is retained:

- `Langlands.LocalClassField.closedCommutator_le_kernel` (theorem).

The original elaborated module contains 53 declarations, including generated helpers.

#### Norms

- `Langlands.LocalClassField.normUnits` (def): same public name and complete declaration.
- `Langlands.LocalClassField.normSubgroup` (def): same public name and complete declaration.
- `Langlands.LocalClassField.normToImage` (def): same public name and complete declaration.
- `Langlands.LocalClassField.NormQuotient` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.normQuotientProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.normQuotientTowerProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.normQuotientTowerNorm` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localInclusion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localNorm` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localNormSubgroup` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.LocalNormQuotient` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.localNormQuotientProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localNormQuotientTowerProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localNormQuotientTowerNorm` (def): same public name and complete declaration.

Private source helpers, whose source text is retained:

- `Langlands.LocalClassField.tower_normSubgroup_le` (theorem).

The original elaborated module contains 30 declarations, including generated helpers.

#### Transfer

- `Langlands.LocalClassField.continuousTransfer` (def): same public name and complete declaration.
- `Langlands.LocalClassField.transferToAbelianization` (def): same public name and complete declaration.
- `Langlands.LocalClassField.abelianizedTransfer` (def): same public name and complete declaration.
- `Langlands.LocalClassField.subgroupInclusion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.subgroupOfEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.subgroupAbelianInclusion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.subgroupAbelianTransfer` (def): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteFixingFiniteIndex` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteTransferToFixing` (def): same public name and complete declaration.
- `Langlands.LocalClassField.absoluteFixingAbelianInclusion` (def): same public name and complete declaration.
- `Langlands.LocalClassField.pullbackFixingSubgroup` (def): same public name and complete declaration.
- `Langlands.LocalClassField.pullbackFixingSubgroup_open` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.pullbackFixingFiniteIndex` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.pullbackTransferToFixing` (def): same public name and complete declaration.
- `Langlands.LocalClassField.pullbackFixingAbelianInclusion` (def): same public name and complete declaration.

Private source helpers, whose source text is retained:

- `Langlands.LocalClassField.transfer_continuous` (theorem).

The original elaborated module contains 41 declarations, including generated helpers.

#### Units

- `Langlands.PadicField.TopologicalData.multiplicativeTopology` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.valuationRing` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.unitSubgroup` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.principalUnitSubgroup` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.integerUnitsEquiv` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.integerUnitsInclusion` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.integerUnitsInclusionContinuous` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.residueUnits` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.principalUnitsEquiv` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.TruncatedIntegers` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.truncatedReduction` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.truncatedUnitsReduction` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.truncatedUnitsReductionContinuous` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.congruenceUnits` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.unitFiltration` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.UnitQuotient` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.unitQuotientProjection` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.unitQuotientReduction` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.unitQuotientProjectionContinuous` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.unitQuotientReductionContinuous` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.orderHom` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.ValuationQuotient` (abbrev): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.valuationQuotientProjection` (def): same public name and complete declaration.
- `Langlands.PadicField.TopologicalData.valuationQuotientProjectionContinuous` (def): same public name and complete declaration.

The original elaborated module contains 39 declarations, including generated helpers.

#### WeilAbelianization

- `Langlands.LocalClassField.WeilQuotients.Abelianization` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.projection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.degree` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.toGroupAbelianization` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.inertia` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.inertia_eq_image` (theorem): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.UnramifiedQuotient` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.unramifiedProjection` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.unramifiedDegreeEquivRange` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.unramifiedDegreeEquiv` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.characterDescent` (def): same public name and complete declaration.
- `Langlands.LocalClassField.WeilQuotients.map` (def): same public name and complete declaration.
- `Langlands.LocalClassField.localPullbackAbelianization` (abbrev): same public name and complete declaration.
- `Langlands.LocalClassField.localPullbackToGalois` (def): same public name and complete declaration.

The original elaborated module contains 30 declarations, including generated helpers.

#### UnitNormStatement

The six names are retained with their full original proposition bodies and
independent universes `u,v`:

- `Langlands.LocalClassField.UnramifiedUnitNorms`.
- `Langlands.LocalClassField.UnramifiedNormMembership`.
- `Langlands.LocalClassField.UnramifiedCyclicNormQuotient`.
- `Langlands.LocalClassField.UnramifiedNormCharacterCriterion`.
- `Langlands.LocalClassField.AbelianUnitNormIndex`.
- `Langlands.LocalClassField.UnitNormTheorems`.

The untouched NormStatement still defines
`Langlands.LocalClassField.NormGroupTheorems.{u,v}` as precisely
`FiniteNormProperties.{u,v} ∧ NormSubgroupExistence.{u}`.
Neither it nor any existing proof source is edited by this contribution.

#### ReciprocityRelations

Every named source declaration keeps its name and complete declaration:
`WeilReciprocityCandidate` (abbrev); `candidateGaloisHom`,
`GeometricOrderRelation`, `LocalReciprocityCandidateRelation`,
`CompletionComparisonRelation`, `LocalReciprocityExistence`,
`weilCandidateCharacterEquiv`, `AbsoluteNormRelation`,
`AbsoluteTransferRelation`, `WeilNormRelation`, `WeilTransferRelation` and
`RelativeWeilReciprocityRelation` (def), all in namespace
`Langlands.LocalClassField`. The elaborated module contains 31 declarations,
including generated helpers.

#### ResidueNormalization

Every named source declaration keeps its name and complete declaration. In
namespace `Langlands.LocalClassField.ResidueNormalization`: the defs
`geometricFrobeniusClass`, `HasGeometricResidueAction` and
`GeometricNormalization`, and the theorems `geometricFrobeniusClass_residue`,
`mk_eq_geometricFrobeniusClass_iff`,
`hasGeometricResidueAction_iff_inverse_power`,
`geometricNormalization_iff_residue`, `normalized_uniformizer` and
`normalized_unit`. In namespace
`Langlands.LocalClassField.ResidueNormalization.Canonical`: the theorem
`residueField_finite`, the defs `geometricFrobeniusClass` and
`GeometricNormalization`, and the three anonymous local instances. The
elaborated module contains 33 declarations, including generated helpers.

#### ProfiniteReciprocityStatement

Every named source declaration keeps its name and complete declaration, all
defs in namespace `Langlands.LocalClassField`: the relation
`GeometricProfiniteReciprocityRelation` and the propositions
`LocalFiniteIndexSubgroupsOpen`, `ProfiniteReciprocityExistenceUniqueness`,
`ProfiniteReciprocityCompletion` and `ProfiniteReciprocityCharacterTransport`
(universe `u`), and `ProfiniteReciprocityNormFunctoriality`,
`ProfiniteReciprocityTransferFunctoriality` and `ProfiniteReciprocityTheorems`
(independent universes `u,v`). The elaborated module contains 20 declarations,
including generated helpers.

#### TateNormQuotient

Every named source declaration keeps its name and complete declaration, all
in namespace `Langlands.ClassFieldTheory.Local` with universes `u,v`: the defs
`baseUnitNormClass`, `normQuotientEquivInvariantQuotient` and
`tateZeroEquivNormQuotient`, and the theorems `normToInvariants_units`,
`baseUnitNormClass_ker`, `baseUnitNormClass_surjective`,
`normQuotientEquivInvariantQuotient_mk` (simp) and
`tateZeroEquivNormQuotient_zeroClass`. The elaborated module contains 12
declarations, including generated helpers.

#### Herbrand.Absolute

Every named source declaration keeps its name and complete declaration, all
in namespace `Langlands.Ramification.Padic` with universes `u,v`: the abbrevs
`finiteGaloisPadicField` and `absoluteFiniteExtension`; the defs
`absoluteFiniteRestriction`, `absoluteUpperRamificationGroup` and
`localAbelianUpperRamificationGroup`; the instance
`absoluteUpperRamificationGroup_normal`; and the theorems
`mem_absoluteUpperRamificationGroup_iff`,
`mem_absoluteUpperRamificationGroup_iff_lower`,
`absoluteUpperRamificationGroup_le_comap`,
`absoluteUpperRamificationGroup_map_restriction_le`,
`absoluteUpperRamificationGroup_isClosed`,
`absoluteUpperRamificationGroup_antitone`,
`absoluteUpperRamificationGroup_neg_one` (simp),
`absoluteUpperRamificationGroup_of_le_neg_one`,
`mem_localAbelianUpperRamificationGroup_iff`,
`mem_localAbelianUpperRamificationGroup_iff_finite` and
`localAbelianUpperRamificationGroup_antitone`. The elaborated module contains
41 declarations, including generated helpers.

#### CyclicNorm

Every named source declaration keeps its name and complete declaration, all
in namespace `Langlands.ClassFieldTheory.Local` with universes `u,v`: the defs
`invariantUnitsEquiv`, `invariantNormProjection`, `invariantsModNormEquiv`,
`cyclicH2InvariantsEquiv` and `cyclicH2NormEquiv`, and the theorems
`invariantUnitsEquiv_norm`, `invariantsModNormEquiv_mk` and
`invariantsModNormEquiv_symm_projection`. Its private source helpers
`invariantNormProjection_surjective`, `invariantNormProjection_ker`,
`submoduleQuotientAddEquiv`, `quotientByKernelEquiv`,
`cyclicKernelEquivInvariants` and `cyclicKernelEquivInvariants_map_range`
keep their source text; since the module itself does not move, their internal
names are unchanged. The elaborated module contains 39 declarations, including
generated helpers, and 3 additional compiler-generated names.

#### ReciprocitySystem

The Lean source is unchanged; it imports ReciprocityRelations, whose imports
moved. Its 87 compiled declarations in namespace `Langlands.LocalClassField`,
including generated helpers, and its 2 additional compiler-generated names are
compared like the importers above.

### Source-preservation fingerprints

The full original source hashes identify the starting Lean files. The
non-import fingerprint hashes the complete original bytes with import lines
removed, retaining all other source text; the corresponding canonical file must
have the same fingerprint. The original Markdown is retained in the canonical
pair except for module-path references and this migration documentation. The
original Completion, FiniteArtin and Transfer Markdown used CRLF line endings;
the canonical files use LF throughout, with the same text.

| Basename | Original Lean SHA256 | Non-import SHA256 |
| --- | --- | --- |
| Completion | `bf1f43578844bb95ae9a8e17965524400bd0dfa723cb8d565e3937343d7b3d36` | `0af82f5a17be049fa8142cae6f60eb72f86dcf837ae3299a074e734277c3baac` |
| FiniteArtin | `9c784b84248abb80114d1fc34824c26a5b937616e58113ee47650efb595b115a` | `2d44e2a554c10a38c9a6ae27ddca8826d591e25980e15ee79c919811ea7817a8` |
| Galois | `c0b4086267f4070f4f04d9d8fea1f90f6dbf1fba7b5f9f833a6d04783340c4a6` | `79ab65ce8f53ad265131dc426b149f9e91cea51ab3a2c6c15b9caa05be7ed70e` |
| Norms | `696b8c578a372037c4729160b4be63fac3365e96360abf5b50b8b546fe994d87` | `1d5787f5b779f3fa5dc126097d754df0f34559725cc7968d135ee9082f705459` |
| Transfer | `bac9e22ed68e0bd726083bfdfb01f53e2455017207c36c5a00934b5007b81c5d` | `6ae76463d6690ccda8b0c3b3cc78de291d5eafe2c46c94b6388b64bb678f7db6` |
| Units | `4c0a4ea98a2acee28712326b598dff39bcb1300de0d77cd94aa8f90b8a6499a9` | `006a857a4f20addecefed1fb11bc358c4bbb295d8f95dcde7c3709e7a21ca27d` |
| WeilAbelianization | `0c3361165671b4bb2d775f057736299fba9024aab11e40eb76ecd83ccc4c1208` | `47a3e4817064a2df24801d317caef06a62bf46563145367b2cc742f8dcaceb76` |

The seven importers are edited in place. Their non-import fingerprints are
unchanged:

| Importer | Original Lean SHA256 | Non-import SHA256 |
| --- | --- | --- |
| UnitNormStatement | `a1c7558f7336d87011b02ed05ada93b4f913b93d0a52e2c8b2034006c115972b` | `0c9d85564b18732d5a480b2663aa296209952cf8ed84feda4da857849561ecaa` |
| ReciprocityRelations | `05a7a6ace02721bac317905529ae5c9d43f68ed039af191266571e18882d5b2d` | `268bbbc06677c7629aa2ce70da0916c4a9d308575b6fc960a05febbd2d77b6e3` |
| ResidueNormalization | `419e5e833bfd229a6f1a662b72e9a649eee678da5943bdad33bf7184060aa06c` | `7d2e4e5a9c7d9d1af8755900caf6596e927d136f3bfaa29eda5b16b74b70d228` |
| ProfiniteReciprocityStatement | `74ebc8694934b9c215db662d412f19a816a7caf97208be28558d43ace9e17fe6` | `1d966b288e75701438785f8b1ee866616e03599d3a1133d565d689ce11ddb374` |
| TateNormQuotient | `f0de24fb56f583c2d4bdc64414dccd621c96d4a3556f8fa1adbc164f66bb3f8a` | `3af73ebf37050f8ec8888eb033ddc3518b6260f7d2fbbab879e1f859efee71d1` |
| Herbrand.Absolute | `245093538f558bebdba63899a68d257cc95ea8726e601bc766cd2af93a4857fd` | `e59cea57b1b6e6aab47e2b99f134d37cb488289ead21786961e7a0f147331495` |
| CyclicNorm | `e9980a9820aa432a60f1be05361b448620602f9cd14b6a8e65a80da95587ab2c` | `29ea32df4d1e046bdbcf373166c7e5d3be86bcb4eb70327624eb07476f7f5841` |


### Private compiler names and compatibility

Lean gives private helpers internal names containing their defining module.
Moving a module changes that internal module component, including references
from elaborated proof bodies. Those private names are not public interfaces.
The preservation comparison identifies exactly the seven old/new module prefixes
when comparing serialized kernel expressions; it does not erase hypotheses,
universe parameters, binder information or any expression node. Public names
are compared without renaming. This accounts for module-qualified private names
without claiming literal equality of their unnormalized printed encodings.

### Coordination and integration sequence

Before editing, Worker 63 checked Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. Apart from the imports among the
seven moved modules, UnitNormStatement was the only module importing an old
path, no wiki, notes or Markdown page linked to one, and the seven destination
paths were unused. The Library then advanced to
`a6142598ca59c1c7c4408d715a4ae77cfe7469bc`, which added only the unrelated
`Langlands.Weil.Local.ExtensionResidue`, then to
`68e8013fc4fed0de284fd849695676aca2e0c32d`, then to
`3b5205fa6ae98b1b2f57b8bfc33e99d78771f240`, then to
`0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf`, then to
`227d9fba27524d01ebfaa754094bdf4055e5b456`, then to
`6a8237b859e39d797365602ce6a1d71b23cab788`, then to
`22b4f024e0d4218752e970d09329d1799f6d81d1`, then to
`00f9ac4d66cfd40043d36dbe31ea364e1316cde9`, and then to the base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Among unrelated modules, the
commit 68e8013f published Worker 21's ReciprocityRelations and
ResidueNormalization, the commit 3b5205fa published Worker 10's
ProfiniteReciprocityStatement, the commit 0fbab0ee published Worker 42's
TateNormQuotient and Worker 21's ReciprocitySystem, the commit 22b4f024
published Worker 68's `Langlands.LocalFactor.Ramification.Herbrand.Absolute`,
and the commit 00f9ac4d published Worker 28's
`Langlands.ClassFieldTheory.Local.CyclicNorm`.
ReciprocityRelations, ResidueNormalization, ProfiniteReciprocityStatement,
TateNormQuotient, Herbrand.Absolute and CyclicNorm imported old paths and are therefore
updated here; ReciprocitySystem imports only
ReciprocityRelations and `Langlands.LocalField.Canonical`, so only its
Markdown sentence about those imports changes. The commit 227d9fba added six
unrelated pairs, the commit 6a8237b8 added eleven more, including
`Langlands.ClassFieldTheory.Local.FixedFieldUnits`, the commit 22b4f024
added 31 unrelated pairs besides Herbrand.Absolute, the commit 00f9ac4d added
nine unrelated pairs besides CyclicNorm, including
`Langlands.ClassFieldTheory.Local.RelativeH1Proof`, and the base c139df9c added
seven unrelated pairs and changed no existing file; none of them imports an old
path. One of the latter, `Langlands.LocalFactor.RankOne`, imports
ReciprocityRelations, whose own path does not move, so it compiles against the
migrated tree without edits. At this base no other Library module imports an old path, and the Library
has not changed any of the seven pairs, UnitNormStatement or a destination path.
Two other Library pages link to old paths, both separately reviewed notes. The
published module atlas note, `notes/library/module-atlas.md`, links the old
Completion and FiniteArtin Markdown and describes this consolidation as planned.
Worker 21's coverage note, `notes/class-field-theory/local-coverage.md`,
published at 6a8237b8, links all seven old Markdown paths in its module table
and says the modules remain there until this move is published. The old
Markdown files remain as pointer pages to the canonical documentation, so these
links still resolve. Both notes are to be updated after this migration is
published; Worker 21 agreed to that sequence for the coverage note.

No staged candidate edits the seven pairs, the seven importers,
ReciprocitySystem or a destination path. One staged statement candidate, Worker
92's `Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyStatement`, imports
the old Units path and keeps compiling through its shim. Another staged
statement candidate adds the new module
`Langlands.LocalClassField.UnramifiedAlgebraStatement` under the old directory;
it is not one of the seven moved paths and imports no old path, so this
migration does not affect it. Shared drafts of Worker 10's statement task still
import old paths and also keep compiling through the shims.

Worker 63 asked Workers 21, 10, 4, 42, 49, 60 and 34, who maintain local
class-field, class-formation, ramification and atlas work, about pending edits
or imports of the old paths. Worker 21, author of the seven construction pairs,
confirmed that no pending candidate or private draft edits them and that
declaration namespaces stay `Langlands.LocalClassField`. Worker 21 also
agreed to the import-line edits to the published ReciprocityRelations and
ResidueNormalization and has no pending edit to either. Worker 21 accepted
the one-sentence edit to ReciprocitySystem.md, and Worker 10 was told about the
corresponding edit to ProfiniteReciprocityStatement. Worker 4 has no local
edit or pending candidate touching the seven pairs. Worker 10 has no pending edit to UnitNormStatement, does not
object to an import-only relocation, and asked that the shims be kept because
other statement work still imports the old Completion, FiniteArtin and Units
paths. Worker 42 planned to switch TateNormQuotient to the canonical Norms path
after publication. Since that pair was published first, this migration makes
the import-only edit, and Worker 42 was told. Worker 60's other published ramification modules import no old path, and
Worker 60 planned to use the canonical Galois path once it is published.
Worker 68, author of Herbrand.Absolute, and Worker 28, author of CyclicNorm,
were told about the import-line edits to their modules; Worker 68 has no
pending edit to Herbrand.Absolute and agreed that the migration proceed. Worker 34's documentation
atlas describes this module map without Lean edits. Worker 49 had not replied
when this ledger was written; the staging check above covers submitted work.

The move installs the canonical construction pairs, replaces the old paths by
shims and changes the seven current Library importers. Other workers' frozen
candidates and private drafts are not edited here; any that import an old path
keep compiling through the shims. Shims must remain until every consumer
imports the canonical paths; removing them is separate later work.

### Validation status

All checks below ran on the exact migrated tree in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The source check, pairing check
and whole-tree compilation ran over Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. The compiled-declaration
comparison ran over the preceding commit
`00f9ac4d66cfd40043d36dbe31ea364e1316cde9`. The base c139df9c only adds
seven pairs that none of the fifteen compared modules imports, so every input
of that comparison is byte-identical at the base.

- Source check: each original Lean file has the SHA256 in the tables above.
  Every canonical file and every importer has the same non-import fingerprint as
  its original, and the textual differences are import lines only: FiniteArtin
  2, Transfer 1, WeilAbelianization 1, UnitNormStatement 2,
  ReciprocityRelations 5, ResidueNormalization 1,
  ProfiniteReciprocityStatement 2, TateNormQuotient 1, Herbrand.Absolute 1 and
  CyclicNorm 1.
  Completion, Galois, Norms and Units are byte-identical to their originals.
  Each shim is exactly the single line
  `import Langlands.ClassFieldTheory.Local.X`.
- Compiled-declaration comparison: a private audit compiled the original
  Library files and the migrated tree separately and compared every constant of
  the fifteen affected modules. These are the 312 constants of the seven moved
  modules, the 7 of UnitNormStatement, the 31 of ReciprocityRelations, the 33
  of ResidueNormalization, the 20 of ProfiniteReciprocityStatement, the 12 of
  TateNormQuotient, the 41 of Herbrand.Absolute, the 39 of CyclicNorm and the
  87 of the unchanged ReciprocitySystem. For each constant, the digests of the type, value,
  structure fields, flags and axioms are equal, as are the universe parameters,
  the per-module counts and the normalized import lists. The four private
  helper names of the moved modules are compared modulo the module prefix, as
  described above. Every affected module uses only the axioms `propext`,
  `Classical.choice` and `Quot.sound`. The shims declare no constants.
- Pairing: each of the 21 edited or new Lean files has a nonempty same-stem
  Markdown file, and every Lean file in the tree is paired.
- Whole tree: all 480 Lean modules of the migrated tree compiled with 0 errors
  and 0 warnings.

Development checks do not establish independent acceptance or publication.
