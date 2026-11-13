# The chosen valuation ring of the separable closure of a local field

This module adapts NYLL source units M249.001, M249.002, M249.003 and M249.006.
Its main export is the data definition
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring`: for a
nonarchimedean local field `K`, a chosen valuation subring of
`SeparableClosure K`. The separate unit M249.007 proves that it lies over the
valuation ring of the canonical valuation of `K`, so mathematically it is a
choice of a place `w | v` of the separable closure above the place `v` of `K`.
In the source, the finite local reciprocity construction (the local residue
datum M249.024) takes its residue fields and decomposition groups from this
choice.

The three other declarations are the auxiliary pieces of the source that the
definition is built from. They are kept in the stable internal namespace
`Langlands.NYLL.PortInternal.M249` given by the port inventory:

| Unit | Adapted declaration | Kind |
| --- | --- | --- |
| M249.001 | `Langlands.NYLL.PortInternal.M249.d001` | local instance (data) |
| M249.002 | `Langlands.NYLL.PortInternal.M249.d002` | local instance (Prop) |
| M249.003 | `Langlands.NYLL.PortInternal.M249.d003` | definition (data) |
| M249.006 | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` | definition (data) |

No theorem is stated or proved here, and the module declares no global
instance.

## Common parameters

Every declaration takes, as its only parameters, the section variables of the
source (lines 45–46):

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

So `K` is a field in `Type` (universe zero, as in the source) that is a
nonarchimedean local field in the sense of Mathlib's class
`IsNonarchimedeanLocalField`, with its given valuative relation and topology.
`AlgebraicClosure K` is Mathlib's chosen algebraic closure and
`SeparableClosure K` is Mathlib's separable closure of `K`, defined as the
subfield `separableClosure K (AlgebraicClosure K)` of `AlgebraicClosure K`
viewed as a type.

## The declarations

### M249.001: `d001`

```lean
local instance d001 :
    Algebra (SeparableClosure K) (AlgebraicClosure K) :=
  (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
```

The algebra structure given by the inclusion of the separable closure into the
algebraic closure: `(separableClosure K (AlgebraicClosure K)).val` is the
`K`-algebra inclusion of the intermediate field. Its algebra map sends an
element of `SeparableClosure K` to itself in `AlgebraicClosure K`.

Mathlib also has an instance of this class: `SeparableClosure K` is an
`abbrev` for the intermediate field, so `IntermediateField.toAlgebra` applies.
The two agree definitionally, but only after unfolding beyond instance
transparency (see Checks). The source nevertheless declares its own local
instance, and the port keeps it so that the later units can install the same
instance as the source.

### M249.002: `d002`

```lean
local instance d002 :
    IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
```

The tower `K → SeparableClosure K → AlgebraicClosure K` commutes; this holds
by definition, since both composite maps send `x : K` to `x`. This is a
proposition.

Both instances are declared with `local instance`, as in the source. Importing
this module therefore makes `d001` and `d002` available as declarations but
does not add global typeclass instances. A consuming module that needs them,
as the source's later declarations do, restores the source behaviour with

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M249.d001
  Langlands.NYLL.PortInternal.M249.d002
```

### M249.003: `d003`

```lean
noncomputable def d003 :
    ValuationSubring (AlgebraicClosure K) :=
  Classical.choose
    (Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
      (L := AlgebraicClosure K) (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation)
```

A valuation subring of `AlgebraicClosure K` chosen by Chevalley's extension
theorem. The ingredients are published:

- `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K` (M248.001, in
  [the canonical complete DVF](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Canonical.md))
  packages the canonical valuation of `K` as a complete discrete valuation
  field; `.valuation` is that valuation.
- `exists_extension_valuationSubring` (M110.003, in
  [the Chevalley extension proof](../../../../../../ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension/U003/Proofs.md))
  proves, for any field extension `L` of `K` and any valuation `vK` of `K`,
  that there is a valuation subring `B` of `L` such that the valuation ring
  `𝒪_vK` of `vK` maps into `B`, the induced map `𝒪_vK → B` is a local
  homomorphism, and `x ∈ B ↔ x ∈ 𝒪_vK` for `x : K` (with `x` viewed in `L`).

`Classical.choose` picks such a `B` for `L = AlgebraicClosure K` and the
canonical valuation of `K`. The choice is not canonical. The source theorem
M249.009 (not ported here) shows that every valuation subring of
`SeparableClosure K` whose valuation extends the valuation of `K` equals
`localSeparableValuationSubring K`, so the ring defined below does not depend
on the choice. The source declares this definition `private`;
here it is a public declaration under the internal name, so that the later
units of the same source module can use it.

### M249.006: `localSeparableValuationSubring`

```lean
noncomputable def localSeparableValuationSubring :
    ValuationSubring (SeparableClosure K) :=
  (Langlands.NYLL.PortInternal.M249.d003 K).comap
    (algebraMap (SeparableClosure K) (AlgebraicClosure K))
```

The preimage of the chosen valuation subring `d003 K` of `AlgebraicClosure K`
under the inclusion `SeparableClosure K → AlgebraicClosure K`, as a valuation
subring of `SeparableClosure K` (Mathlib's `ValuationSubring.comap`). The
algebra map is the one given by `d001`, which is installed with
`attribute [local instance]` for this definition only. In other words, it is
the intersection of `d003 K` with the separable closure.

The published proof units that will follow (M249.007, M249.008, from separate
modules in the same folder) state that `localSeparableValuationSubring K`
pulls back to the valuation ring of the canonical valuation of `K`, and so
defines a valuation that extends it.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of
`localSeparableValuationSubring` reported kind `definition`, no level
parameters, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. A private check that imports this module confirmed:

- `d001 K` equals the instance that Mathlib's instance search finds for
  `Algebra (SeparableClosure K) (AlgebraicClosure K)` by `rfl`, but not by
  `with_reducible_and_instances rfl`;
- after `attribute [local instance] d001 d002`, instance search returns `d001`
  (checked by `with_reducible rfl`);
- `z ∈ localSeparableValuationSubring K` is definitionally
  `(z : AlgebraicClosure K) ∈ d003 K`, for `z : SeparableClosure K`.

## Imports and scope

- `Mathlib.FieldTheory.IsSepClosed` supplies `SeparableClosure`,
  `separableClosure` and `AlgebraicClosure`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`
  supplies `localCompleteDVF` and, through its imports, Mathlib's
  `IsNonarchimedeanLocalField`.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U003.Proofs`
  supplies `exists_extension_valuationSubring`.

The four source imports (`ResidueActionIndex`, `FiniteIntegralClosure`,
`FiniteExtensionCorrespondence` and `FiniteExtensionCompleteDVF`) serve the
rest of the source module; the three imports above are all that these four
declarations use.

Only M249.001–M249.003 and M249.006 are adapted. The source's private lemma
M249.004 and private instance M249.005 (lines 66–84), which concern the
auxiliary ring `d003 K` itself, are not ported as declarations. In the source,
M249.004 is used only in M249.005 and in the proof of M249.007; its proof is
inlined into the separate proof unit of M249.007. M249.005 is not referred to
by name anywhere in the source module; if the port of a later unit turns out to
need it through instance search, it can be added then. The other source units of the module
(M249.007 onwards) are not part of this module.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L45-L92)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`, the
value recorded for M249 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m249).

| Partition unit | Original declaration in `LocalClassFieldTheory` | Original lines | Adapted declaration |
| --- | --- | --- | --- |
| M249.001 | local instance `localSeparableClosureAlgebra` | 48–50 | local instance `Langlands.NYLL.PortInternal.M249.d001` |
| M249.002 | local instance `localSeparableClosureScalarTower` | 52–54 | local instance `Langlands.NYLL.PortInternal.M249.d002` |
| M249.003 | private def `localAbsoluteValuationSubring` | 58–64 | `Langlands.NYLL.PortInternal.M249.d003` |
| M249.006 | def `localSeparableValuationSubring` | 86–92 | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` |

The line ranges include the doc comments (lines 58–59 and 86–88). The source
module opens namespace `LocalClassFieldTheory` (line 31), works in
`noncomputable section` (line 39) and declares the section variables at lines
45–46; the adapted module does the same in `Langlands.NYLL.PortInternal.M249`
and `Langlands.NYLL.LocalClassFieldTheory`.

Worker 3 made these changes on 13 November 2026:

- renamed the two local instances and the private definition to the internal
  names `d001`, `d002` and `d003` listed in the partition, and made `d003`
  public (not `private`) under that name; the two instances remain local;
- added the `Langlands.NYLL` prefix to the namespace of
  `localSeparableValuationSubring`. Its body refers to `d003` instead of the
  source name `localAbsoluteValuationSubring`, and uses `d001` through
  `attribute [local instance]`, which replaces the source's file-wide local
  instance;
- spelled out the published names
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring`
  and `Langlands.NYLL.LocalFieldTheory.localCompleteDVF` in the body of
  `d003`, in place of the source's `ValuationTheory…` and opened
  `LocalFieldTheory` spellings;
- omitted the source's `open` lines (lines 33–35 and 41–43), which these
  declarations do not need;
- kept the parameters, result types and bodies otherwise unchanged;
- added doc comments to `d001` and `d002` (the source instances have none)
  and prefixed the doc comment of `d003` with its source unit; the doc comment
  of `localSeparableValuationSubring` is the source's;
- replaced the source imports by the three imports above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `LocalResidueDatum.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
