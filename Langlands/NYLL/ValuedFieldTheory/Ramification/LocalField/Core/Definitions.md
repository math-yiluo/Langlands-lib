# Lower and upper ramification groups of a finite Galois local extension

This module adapts exactly M327.004 and M327.005 from Naganori
Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean).
M327.004 occupies lines 87–100 (declaration at line 91) and M327.005
lines 102–113 (declaration at line 104). Lines 1–135 of the original
file, including its imports, namespaces, the M327.001 uniqueness alias
and the private pullback declarations M327.002/.003, were read
directly. The whole-file SHA-256 is
`d0e79ce27df3b1f7481d2e6c89473f600acaf21f0cf4b678e29ba97a90792ecb`.

## Complete interfaces and defining expressions

Both declarations lie in `Langlands.NYLL.RamificationTheory.LocalField`.
The module opens `Langlands.NYLL.LocalFieldTheory` and
`Langlands.NYLL.RamificationTheory.HilbertRamification`. With those
openings their complete interfaces and bodies are:

```lean
noncomputable def localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  letI : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  Higher.lowerRamificationGroup
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L) t

noncomputable def localUpperRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  letI : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  Higher.upperRamificationGroupOfUniqueExtension
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L) t
```

Both definitions have no universe parameters. The two fields `K` and
`L` are explicit and lie in `Type` (universe 0). The field, algebra,
finite-dimensionality, Galois, valuative-relation, topology and
local-field structures are instance arguments. The real index `t` is
explicit. Each result is a subgroup of Mathlib's actual algebra
automorphism group `Gal(L/K) = L ≃ₐ[K] L`. There are no other
parameters. In particular, `L` carries no supplied valuation or
topology, and neither interface has a `HasExtension`, uniqueness,
integral-closure, finite integer-module or inverse-law premise.

The bodies use the published canonical complete DVF
[`localCompleteDVF K`](../../../LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Canonical.md)
of the base and the published named chosen complete DVF
[`chosenLocalExtensionCompleteDVF K L`](../../../LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Chosen.md)
of the extension. Both are forgotten to DVFs by the published
abbreviation `CompleteDVF.toDVF`. That abbreviation is the path
`CompleteDVF → HenselianDVF → DVF`. The valuation-extension instance
needed by the generic API is installed only locally by `letI`. Its
value is the existential witness `Classical.choose` of the published
theorem
[`chosenLocalExtension_properties`](../../../LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/ChosenPropertiesProof.md).
That theorem states that some `HasExtension` instance exists for
which the chosen valuation ring is the integral closure of the base
valuation ring and is a finite module over it. `HasExtension` is a
`Prop`, so every witness is definitionally equal by proof
irrelevance. The choice of witness therefore does not affect either
group.

The uniqueness argument is the published theorem
[`chosenLocalExtension_uniqueValuationExtension`](../../../LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/ChosenUniquenessProof.md)
at comparison universe 0. Its statement says that every valuation of
`L` in universe 0 extending the base valuation is equivalent to the
chosen valuation. This is definitionally the published five-universe
predicate
[`DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}`](../../HilbertRamification/RealLowerGroups/UniqueExtension.md)
for the two DVFs above, which is the type expected by the generic
groups. Both reused theorems assume `[Algebra.IsSeparable K L]`.
Lean derives it here from `[IsGalois K L]`.

The lower group is the published actual real lower ramification group
[`Higher.lowerRamificationGroup`](../../HilbertRamification/RealLowerGroups/LowerGroup.md)
for these valuations. It consists of the automorphisms `σ` such that
`σ a - a` lies in `m ^ (Int.ceil (t + 1)).toNat` for every `a` in the
chosen valuation ring. Here `m` is the maximal ideal of that ring, and
`σ` acts on it through the published restriction
`valuationSubringAutOfUniqueExtension`. The upper group is
the published
[`Higher.upperRamificationGroupOfUniqueExtension`](../../HilbertRamification/HerbrandFunction/Definitions.md)
with identical arguments. By that definition it is the same actual
lower group evaluated at the actual inverse Herbrand function
`Higher.inverseHerbrandFunctionOfUniqueExtension` attached to the same
valuations. A check that both sides are definitionally equal (`rfl`)
compiled for

```lean
localUpperRamificationGroup K L t =
  localLowerRamificationGroup K L
    (Higher.inverseHerbrandFunctionOfUniqueExtension
      (base := (localCompleteDVF K).toDVF)
      (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
      (chosenLocalExtension_uniqueValuationExtension.{0} K L) t)
```

with the same local instance. That check is not part of this module.
No valuation, field or automorphism group is replaced, transported or
supplied by the host.

## Definition scope

These are data definitions for every finite Galois extension of a
nonarchimedean local field with both fields in `Type`. This unit
proves no laws about the groups. In particular, it delivers no
nonpositive-index laws, residue-kernel equality, filtered
reciprocity, host inertia or finite Type 0 reciprocity. It also
establishes no arbitrary-universe, cup-comparison or Weil-system
conclusion. Those remain separate statement and proof work.

## Exact source map and modifications

| Unit and original declaration | Adapted declaration |
| --- | --- |
| M327.004, `RamificationTheory.LocalField.localLowerRamificationGroup`, lines 87–100 | `Langlands.NYLL.RamificationTheory.LocalField.localLowerRamificationGroup` |
| M327.005, `RamificationTheory.LocalField.localUpperRamificationGroup`, lines 102–113 | `Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup` |

The namespace gains the prefix `Langlands.NYLL`, and the openings are
reduced to the two namespaces listed above. The binder telescope,
binder kinds, argument order, result type, docstrings and the
`noncomputable` modifiers are retained. The source's
`noncomputable section` is also retained. The only body changes are
the following two.

1. **Local extension witness.** In the source the `HasExtension`
   instance comes from the global instance
   `chosenLocalExtensionCompleteDVF.instHasExtension` (M248.008,
   source file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`,
   line 154). The published port has no such global instance. Instead,
   the existential extension witness is a proved part of
   `chosenLocalExtension_properties`. Each body therefore installs
   `Classical.choose (chosenLocalExtension_properties K L)` with a
   local `letI`. No instance is added to the environment. Because
   the instance type is a `Prop`, this agrees definitionally with any
   other choice of extension proof.
2. **Uniqueness argument.** The source passes its alias
   `LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension`
   (M327.001, line 37). That alias restates the uniqueness theorem in the
   DVF predicate form and proves it by the source uniqueness theorem.
   The published
   `chosenLocalExtension_uniqueValuationExtension.{0} K L` already
   has that type definitionally. It is reused directly at comparison
   universe 0, the universe the source alias uses here. No duplicate
   alias is extracted.

The private source declarations `completeDVFComapAlgEquiv` and
`completeDVFComapAlgEquiv_hasExtension` (M327.002/.003, lines 56–86)
are not used by either body and are omitted. The interleaved later
declarations of the source file are also omitted.

The original wholesale imports are replaced by exactly:

- `Mathlib.FieldTheory.Galois.Basic`, for `IsGalois` and `Gal(L/K)`.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`,
  for `CompleteDVF.toDVF`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenPropertiesProof`,
  for `chosenLocalExtension_properties` and the canonical and chosen
  complete DVFs.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessProof`,
  for `chosenLocalExtension_uniqueValuationExtension`.
- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions`,
  for the actual upper group, and through it the actual real lower
  groups and the uniqueness predicate.

The published dependencies and their paired documentation are
unchanged. Patch P5 from the completed feasibility audit changes only
original line 693, in a later restriction proof. It does not touch
either extracted definition, and this extraction does not use any
later proof adaptation. The partition note
`notes/reuse/nyll-public-port/m313-m336.md` records the M327
boundaries. Its conservative source-order and module-completion edges
do not add premises to these bodies.

## Sources, license and authorship

The registered original is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the
original path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory
was present at preparation.

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned originals,
with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Their inherited notices are preserved unchanged.

Worker 106 contributed the source and interface extraction, the
local-witness design and the dependency and reuse analysis in the task
contract. Worker 1237 checked the original source and the published
interfaces, implemented the extraction and wrote this companion on
3 November 2026. The Lean header records the modifications. The
approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The source used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
