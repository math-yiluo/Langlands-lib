# The finite abstract extension object of an embedded finite Galois extension

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean`
(file SHA-256 `1c30e127abe0416ba3e7ee90cfb1f4c89cda4ea0e45ccf2af457af4322aca51a`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M097.005 | def `finiteGaloisAbstractExtensionOfEmbedding` (docstring 55–56, definition 57–64) | `finiteGaloisAbstractExtensionOfEmbedding` |

The original name is in the source namespace `LocalClassFieldTheory`; the
adapted name is
`Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding`.

The unit lies in the dependency closure of Task 5264 but was not routed to any
task. Worker 5264, who routes that closure, agreed that Task 5799 stages it.
It is a prerequisite of several Task 5799 units in
`FixedFieldIntrinsicReciprocity`. The candidate also carries the helper module
`SeparableUnitsNorm/Finite/Definitions` (the instance
`baseFixingExtensionQuotient_finite`, M096.003), which has its own paired
Markdown.

## Parameters

The definition takes the source section variables of lines 38–39,

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
```

followed by the source binder `(i : L →ₐ[K] SeparableClosure K)`. All fields
are in `Type` (universe zero), as in the source. Both `[FiniteDimensional K L]`
and `[IsGalois K L]` are used, so both are arguments of the elaborated
definition. The full type is

```lean
finiteGaloisAbstractExtensionOfEmbedding (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteGaloisSubextension (PortInternal.M097.d003 K)
```

## Content

Write `Ω = SeparableClosure K`, `E = finiteGaloisFieldRangeOfEmbedding K L i`
(the field range of `i`, an intermediate field of `Ω / K`),
`G₀ = closedFixingSubgroup K Ω ⊥` and `G_E = closedFixingSubgroup K Ω E`.
The base `PortInternal.M097.d003 K` is the published abbreviation for
`intrinsicAbstractBase K`, which unfolds to `G₀` as a closed subgroup of
`intrinsicAbsoluteGalois K = Gal(Ω / K)`.

The definition is the class-formation finite Galois subextension of the base
`G₀` whose top field is `E`, the embedded copy of `L`. Its four fields are:

- `field := finiteGaloisClosedFixingSubgroupOfEmbedding K L i`, which unfolds
  to `G_E`;
- `below := fixingSubgroupLeBase K Ω E`, the inclusion `G_E ≤ G₀`;
- `normal`, normality of `extensionSubgroup G₀ G_E below` in `G₀`;
- `finite := baseFixingExtensionQuotient_finite K Ω E`, finiteness of the
  quotient of `G₀` by that extension subgroup.

The only data is `field`. The other three fields are proofs.

The `normal` proof is copied from the source proof of the instance
`finiteGaloisExtensionSubgroupOfEmbedding_normal` (M090.006, source
`FiniteGaloisRealization.lean`, lines 81–89). It uses `change` to replace
`finiteGaloisClosedFixingSubgroupOfEmbedding K L i` by its unfolding `G_E` and
then closes the goal with `infer_instance`. A separate private check confirmed
that the term
`Subgroup.normal_subgroupOf` applied to
`closedFixingSubgroup_normal K Ω E` (M089.004) and
`finiteGaloisFieldRangeOfEmbedding_isGalois K L i` (M090.003) proves the same
goal. That check is not part of this candidate.

Published components used, all by their Library names:

- `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (M040.001), from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`;
- `Langlands.NYLL.PortInternal.M097.d003` (M097.003), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Initial.Definitions`,
  which unfolds to `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase`
  (M091.003);
- `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding`
  (M090.001), `finiteGaloisClosedFixingSubgroupOfEmbedding` (M090.005) and
  the instances `finiteGaloisFieldRangeOfEmbedding_isGalois` (M090.003) and
  `finiteGaloisFieldRangeOfEmbedding_finiteDimensional` (M090.004), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Realization.Definitions`;
- `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite`
  (M096.003), from the helper module of this candidate,
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Finite.Definitions`;
- through these modules, `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase`
  (M089.002), `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_normal`
  (M089.004), `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002).

The helper module imports
`GaloisExtensionQuotient/Quotient/Definitions` (M089.009 and M089.011,
candidate `154983ac-1004-41d1-ac31-be8597203b1d`), which is published in the
Library at commit `3489c50380b46cfbdad8997457a217e6e8e6a27d`.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The definition is placed in its own file
  `ConcreteReciprocityTransport/Extension/Definitions`.
- The source's private abbreviation `B` (lines 47–48, M097.003) is replaced by
  its published port `Langlands.NYLL.PortInternal.M097.d003`. Both unfold to
  `intrinsicAbstractBase K`, so the type is unchanged.
- The source fills `normal` with `inferInstance`, which finds the instance
  `finiteGaloisExtensionSubgroupOfEmbedding_normal` (M090.006). That instance is
  not in the Library. Its target is published (Worker 4913's candidate
  `8c69bdc8`) as the Prop-valued abbreviation
  `finiteGaloisExtensionSubgroupOfEmbedding_normalStatement` in module
  `FiniteGaloisRealization/Normality/Statements`, but no proof or instance of
  it is published; the instance proof is routed to Task 6409. The port writes
  the source proof of that instance inline, as described under Content.
  `normal` is a proof field, so by proof irrelevance the adapted definition is
  definitionally equal to the source body. A private check confirmed this by
  `rfl`: it stated the source body verbatim (with `B` replaced as above) and
  supplied M090.006 with its source proof as a local instance. The check is not
  part of this candidate.
- The source imports `Mathlib.FieldTheory.Galois.Basic` and five broad NYLL
  modules. The port imports the four modules listed above, which supply every
  declaration the definition uses. The source opens
  `RamificationTheory KummerTheory CyclicCohomology`, `LocalFieldTheory` and
  `ClassFormation`. The port opens `RamificationTheory CyclicCohomology ClassFormation`.
  The others are not used by this definition.
- The docstring, the keyword `def`, the binders, the result type (up to `B`)
  and the `field`, `below` and `finite` fields are copied from source lines
  55–64 without change, inside the source `noncomputable section`.
- No other declaration of the source module is included. The source's private
  abbreviations `G` and `A` and private instance `intrinsicAbsoluteGaloisT2`
  are published as `PortInternal.M097.d001`, `d002` and `d004` in the imported
  module `ConcreteReciprocityTransport/Initial/Definitions`. The definition does
  not use them directly.

## Library and Mathlib comparison

A search of the Library `.lean` files (commit
`3489c50380b46cfbdad8997457a217e6e8e6a27d`) found no declaration named
`finiteGaloisAbstractExtensionOfEmbedding`. It also found no other definition
that builds a `FiniteGaloisSubextension` from an embedding of a finite Galois
extension into a separable closure. The other Library declarations producing a
`FiniteGaloisSubextension` are abstract constructions, forgetful maps or
structure fields: `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.refl`
(the trivial extension `K / K`) and
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.compositum` (the
compositum, represented by the intersection of the two closed subgroups) build new objects from abstract closed
subgroups, not from field embeddings;
`Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.toFiniteGaloisSubextension`
forgets cyclicity of an abstract extension; the structure
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` has the projection
`toFiniteGaloisExtension`; and the structure
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`
has a field `extension` that is supplied as data, not constructed. No module
outside `Langlands/NYLL` uses `FiniteGaloisSubextension`. Mathlib has no
class-formation extension objects.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
