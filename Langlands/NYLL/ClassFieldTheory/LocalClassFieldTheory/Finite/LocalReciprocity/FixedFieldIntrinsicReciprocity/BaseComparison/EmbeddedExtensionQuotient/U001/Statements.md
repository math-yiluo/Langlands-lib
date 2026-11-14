# Embedded extension quotients: transport of extension subgroups

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M274.001 and M274.002:

- `intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement`, for the
  source theorem `intrinsicExtensionSubgroup_iff_ambientEmbeddedField`;
- `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`, for the
  source theorem `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField`
and
`Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`.

Both describe how the published multiplicative equivalence
`intrinsicBaseEquivAmbientEmbeddedField K F i e` (source row M273.006) from
the intrinsic base subgroup of `F` onto the closed subgroup of
`Gal(SeparableClosure K / K)` fixing `i(F)` treats the extension subgroup of
a finite Galois extension `E / F`.

## Common parameters and local data

Both propositions universally quantify, in the source order,

```lean
(K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
  [FiniteDimensional K F] [Algebra.IsSeparable K F]
  [FiniteDimensional F E] [IsGalois F E]
  (j : E →ₐ[K] SeparableClosure K)
```

So `K ⊆ F ⊆ E` is a tower of fields in `Type` (universe zero, as in the
source) with `F / K` finite separable and `E / F` finite Galois, and `j` is
a `K`-algebra embedding of `E` into Mathlib's separable closure
`SeparableClosure K`. There is no valuation, topology or local-field
hypothesis. Both then introduce, as in the source,

```lean
let i := j.comp (IsScalarTower.toAlgHom K F E)
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
letI : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
```

Here `i : F →ₐ[K] SeparableClosure K` is the restriction of `j` to `F`. The
first local instance is the algebra structure of the intermediate field
`separableClosure F (AlgebraicClosure F)`, which is how Mathlib defines
`SeparableClosure F`. The second makes `SeparableClosure K` an `F`-algebra
through `i`. Both propositions then quantify over an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for these structures; the
first one also quantifies over an element `tau` of
`(intrinsicAbstractBase F).toSubgroup`. The Library
`intrinsicAbstractBase F` is the closed subgroup of
`Gal(SeparableClosure F / F)` fixing the bottom intermediate field, which is
the whole group.

After that, both introduce the following local data, verbatim from the
source:

- `jF : E →ₐ[F] SeparableClosure K`, the map `j` regarded as an `F`-algebra
  map (`commutes'` holds by `rfl` because the `F`-algebra structure on
  `SeparableClosure K` is given by `i`, the restriction of `j`);
- `jI : E →ₐ[F] SeparableClosure F := e.symm.toAlgHom.comp jF`, the
  corresponding embedding of `E` into the separable closure of `F`;
- `EI := finiteGaloisAbstractExtensionOfEmbedding F E jI`, the published
  finite abstract extension object of `E / F` attached to `jI` (source row
  M097.005). Its `field` is the closed subgroup of
  `Gal(SeparableClosure F / F)` fixing the field range of `jI`, and `below`
  is the inclusion of that subgroup in the base subgroup
  `intrinsicAbstractBase F`;
- `H₀ := closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)`
  and `J₀ := closedFixingSubgroup K (SeparableClosure K)
  (AlgHom.fieldRange j)`, the closed subgroups of
  `Gal(SeparableClosure K / K)` fixing `i(F)` and `j(E)`;
- `hJH : J₀.toSubgroup ≤ H₀.toSubgroup`, with the source's tactic proof
  (`IntermediateField.fixingSubgroup_le` applied to the inclusion
  `i(F) ⊆ j(E)`, which holds because `i y = j (algebraMap F E y)`).

The Library `extensionSubgroup H J h` (source row M004.002) is the subgroup
`J.toSubgroup.subgroupOf H.toSubgroup` of `H.toSubgroup`; it does not depend
on the inclusion proof `h`.

## The proposition `intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement`

The conclusion is

```lean
tau ∈ extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below ↔
  intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
    extensionSubgroup H₀ J₀ hJH
```

So `tau` fixes the field range of `jI` exactly when its image in `H₀` fixes
`j(E)`.

## The proposition `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`

After the common local data it sets
`psi := intrinsicBaseEquivAmbientEmbeddedField K F i e` and concludes

```lean
(extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below).map
    psi.toMonoidHom =
  extensionSubgroup H₀ J₀ hJH
```

So the image under `psi` of the intrinsic extension subgroup for `E / F` is
the ambient extension subgroup `J₀` inside `H₀`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M273.006, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`) |
| M097.005, `LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions`) |
| M040.001, `ClassFormation.FiniteGaloisSubextension` (fields `field` and `below`) | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`, imported through the M097.005 module) |
| M091.003, `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`, imported through the other modules) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`, imported through the other modules) |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`) |

All of these declarations are published in the Library and are used under the
names above, reached through the source's `open RamificationTheory
CyclicCohomology` line inside the namespace
`Langlands.NYLL.LocalClassFieldTheory`. The statements are otherwise the
source text.

A development check compiled the source proofs of both theorems, unchanged
except that the published proposition
`intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement` (source row
M273.008, whose proof is not yet published) was taken as a hypothesis, against
these two propositions without errors. This only confirms that the statements
are formed as in the source; the proofs belong to the later proof children.

## Relation to other Library and Mathlib declarations

A search of the whole Library found no published declaration that states
either proposition. Both are about
`intrinsicBaseEquivAmbientEmbeddedField` and
`finiteGaloisAbstractExtensionOfEmbedding`, which exist only in this port.
Mathlib's `IntermediateField.mem_fixingSubgroup_iff` and
`IntermediateField.fixingSubgroup_le` describe the fixing subgroups involved,
and the Library's other Galois modules (for example
`Langlands/Weil/Local/ExtensionWeilRangeConjugation.lean` and
`Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean`) transport fixing
subgroups for other constructions; none of them states either proposition.
The already published M274.003 and M274.004 statements
(`ambientEmbeddedExtensionSubgroup_normalStatement` and
`ambientEmbeddedExtensionQuotient_finiteStatement`, module
`...BaseComparison.EmbeddedExtensionQuotient.U003.Statements`) concern the
same ambient subgroups `H₀` and `J₀` but state normality and finiteness.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>).
The complete file was read and its SHA-256 verified as
`6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The M274.001 docstring occupies lines 28–30 and its signature lines 31–70;
its proof occupies lines 71–125. The M274.002 docstring occupies lines
127–128 and its signature lines 129–169; its proof occupies lines 170–217.
The header occupies lines 1–5, the `noncomputable section` line 20, the
namespace line 22 and the `open` lines 24–26.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M274.001, `LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement`, closed Prop target |
| M274.002, `LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField` and `Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase. The
  binders, local `let`/`letI` data and conclusions are otherwise the source
  text, including the tactic proof inside `hJH`.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the Library modules that publish
  `intrinsicBaseEquivAmbientEmbeddedField`,
  `finiteGaloisAbstractExtensionOfEmbedding` and `extensionSubgroup`; these
  import the other Library declarations used.
- The `noncomputable section`, the unused `open LocalFieldTheory` and
  `KummerTheory`, the unused `open ClassFormation` and the
  `open scoped ValuativeRel` are omitted. All other declarations of the
  source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M274.001 and M274.002 statement targets. Their
proofs and the other rows of the source file are not part of this unit.
