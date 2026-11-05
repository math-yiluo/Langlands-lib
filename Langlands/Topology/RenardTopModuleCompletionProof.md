# Actual continuous-linear completion: universal property and canonical adjunction

Worker 1582.

The theorem
`Langlands.Renard.TopModuleCompletion.universalStatements_proof.{u,v,w}`
proves exactly the published closed proposition
`Langlands.Renard.TopModuleCompletion.UniversalStatements.{u,v,w}`.
It imports the existing statement and construction without changing them.
All declarations below lie in `Langlands.Renard.TopModuleCompletion`.

## Source, provenance and scope

The motivating source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The right universal problem is defined on printed p.251 / one-based PDF257;
completion is example 2 on printed p.252 / PDF258.

The printed example literally allows continuous maps, without requiring
linearity or fixing a coefficient field. This proof treats the explicitly
corrected convention of continuous linear maps over a fixed topological field,
with complete separated targets. Its arbitrary unital-ring generalization,
independent universes, canonical additive uniformity, explicit separation
convention, density and embedding assertions, and exact adjunction packaging
are derived internal mathematics. The proof route uses Mathlib's actual
continuous-linear completion and constructs the categorical data from its
extension uniqueness. It does not assume the universal property or an
adjunction.

The uniformly continuous uniform-space theorem has its separate scope. The
fixed-real sequence test and the literal printed all-continuous-maps problem
also retain their own scope; this aggregate neither settles that printed
claim nor provides a counterexample to it. The published statement's bounded
check of the older supplement is not an exhaustive errata claim.

## Hypotheses and exact objects

The first six clauses cover every `R : Type u` with `Ring R`,
`TopologicalSpace R` and `IsTopologicalRing R`. Categorical sources are actual
`TopModuleCat.{v} R` objects. Targets are the existing full subcategory
`CompleteSepModuleCat.{u,v} R`, selected solely by completeness for
`canonicalUniformSpace` and `T0Space`, with all ambient continuous linear maps.
The proof uses the published `completionObject`, `completionFunctor`,
`inclusion`, `canonicalMap`, `canonicalNatTrans` and `extensionHom`.

The concrete source `M : Type v` and target `N : Type w` each have
`AddCommGroup`, `Module R`, `TopologicalSpace`, `IsTopologicalAddGroup` and
`ContinuousSMul R` structures. Only `N` has completeness for its canonical
additive uniformity and `T0Space`. Coefficient, source and concrete-target
universes `u,v,w` remain independent.

Local instances fix the canonical additive uniformities, derive their
`IsUniformAddGroup` and uniformly continuous constant scalar actions, and
extract completeness and separation from selected targets. The completion
uses the existing Mathlib completion uniformity and operations. There is no
free uniform-space parameter that can change the chosen structures.
Source separation is used only in the conditional uniform-embedding result.
There is no norm, dimension, scalar completeness, commutativity,
nontriviality, local compactness, countability or metrizability restriction.
Zero rings and zero modules are covered.

## Implemented proof

`extensionTriangleStatement_proof` proves the chosen extension triangle
pointwise using the published `extensionHom_coe`.

`extensionUniqueStatement_proof` evaluates an arbitrary competitor's triangle
at each original point. This supplies the agreement hypothesis of
`ContinuousLinearMap.fromCompletion_unique`. Extensionality of the full
subcategory and the underlying continuous linear maps gives equality with the
published chosen `extensionHom`. Every continuous linear competitor is covered.

`rightUniversalStatement_proof` constructs initiality of the actual structured
arrow `StructuredArrow.mk (canonicalMap R M)`. To any structured arrow it
assigns the chosen `extensionHom`; the extension triangle makes this a
structured-arrow morphism. Uniqueness follows from the preceding uniqueness
theorem and `StructuredArrow.w`. `Limits.IsInitial.ofUniqueHom` packages the
data, which are wrapped in `Nonempty` as required by the statement.

`completionHomEquiv R M N` is the actual Hom equivalence

```text
(completionObject R M ⟶ N) ≃ (M ⟶ N.obj).
```

Its forward map is exactly
`g ↦ canonicalMap R M ≫ (inclusion R).map g`, and its inverse is exactly
`extensionHom R M N`. The extension triangle and arbitrary-competitor
uniqueness prove the inverse laws.
`completionHomEquivData` supplies its naturality for the existing functors.
Left inverse naturality follows by extension uniqueness: on every original
point, `ContinuousLinearMap.completion_apply_coe` and
`ContinuousLinearMap.fromCompletion_apply_coe` identify both compositions.
Right forward naturality is pointwise reflexivity for the actual full
subcategory inclusion and composition.

`canonicalAdjunctionStatement_proof` applies `Adjunction.mkOfHomEquiv` to this
data, constructing an adjunction of exactly `completionFunctor R` and
`inclusion R`. Its unit at `M` is restriction of the identity of
`completionObject R M`, which simplifies to `canonicalMap R M`; natural
transformation extensionality gives equality with `canonicalNatTrans R`.
`Adjunction.mkOfHomEquiv_homEquiv` proves both specified Hom formulas for the
resulting adjunction.

`canonicalMapStatement_proof` uses `Completion.denseRange_coe` for every source
and `Completion.isUniformEmbedding_coe` under the source `T0Space` hypothesis.
Both refer to the exact canonical map and the uniformities fixed by the
published statement.

`concreteUniversalStatement_proof` uses the published `concreteExtension_coe`
for agreement and `ContinuousLinearMap.fromCompletion_unique` for uniqueness
of every continuous linear competitor. The chosen extension supplies the
explicit exists-unique witness. This proof works directly with the independent
carrier universes and imposes no separation on the source.

`fieldSpecializationStatement_proof` applies the ring results to each
`k : Type u` with `Field k`, `TopologicalSpace k` and
`IsTopologicalDivisionRing k`. The published `CompleteSepVectCat`,
`fieldCompletionFunctor`, `fieldCanonicalNatTrans`, `fieldExtensionHom` and
`fieldConcreteExtension` unfold to the ring constructions. Thus all six
conclusions have exactly the required field aliases and the same independent
universes.

Finally `universalStatements_proof` conjoins these seven proofs in the order
of the unchanged aggregate. It has no outer mathematical premises.
