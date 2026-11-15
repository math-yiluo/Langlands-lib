# The local residue action restricted to a closed subgroup: target

This module states NYLL source unit M250.006 as a closed proposition. It
exports one Prop-valued `def` in namespace
`Langlands.NYLL.LocalClassFieldTheory`:

- `localAbstractFixedResidueAction_applyStatement` (M250.006), for the
  source theorem `localAbstractFixedResidueAction_apply`.

Nothing is proved here. A later proof unit will prove it under the adapted
source name
`Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedResidueAction_apply`.

Mathematically, let `K` be a nonarchimedean local field, let `K^sep` be its
separable closure, and let `B` be the valuation ring
`localSeparableValuationSubring K` of `K^sep` chosen in M249.006. Let `Ω` be
the residue field of `B`. Let `H` be a closed subgroup of `Gal(K^sep/K)` and
let `E = (K^sep)^H` be its fixed field. Every automorphism of `K^sep` over
`K` maps `B` onto itself (M249.010), and so does every automorphism over `E`
(M250.005). So both Galois groups act on `Ω`: an automorphism `τ` sends the
residue class of `b ∈ B` to the residue class of `τ b`.

An element `σ` of `H` fixes `E` pointwise, so it is also an automorphism of
`K^sep` over `E`. The statement says that the two actions of `σ` on `Ω`
agree: acting on `x ∈ Ω` as an element of `Gal(K^sep/K)` (through the
continuous action of M249.020) gives the same result as acting as the
corresponding element of `Gal(K^sep/E)` (through the residue action of
M244.003 over `E`). The source docstring says the same thing: restricting
the local residue action to `H` gives the same underlying automorphism of
the selected residue field as the residue-action map over the fixed field
of `H`.

## The proposition

```lean
def localAbstractFixedResidueAction_applyStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    (sigma : H.toSubgroup)
    (x : selectedResidueField (localSeparableValuationSubring K)),
    localSeparableResidueAlgAction K sigma.1 x =
      residueAlgActionOfEqTop
        (abstractFixedField K (SeparableClosure K) H)
        (localSeparableValuationSubring K)
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma) x
```

The definition has no universe parameters: `K` lives in `Type`, as in the
source. The binders, in order, are the source section variables (lines
33–34) followed by the theorem's own explicit binders `H`, `sigma` and `x`
(lines 103–105).

| Binder | Meaning |
| --- | --- |
| `K : Type` | the base field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| `H : ClosedSubgroup (Gal(SeparableClosure K/K))` | a closed subgroup of the absolute Galois group `Gal(SeparableClosure K/K)` for the Krull topology (Mathlib's `ClosedSubgroup`) |
| `sigma : H.toSubgroup` | an element of `H`; `sigma.1` is the underlying element of `Gal(SeparableClosure K/K)` |
| `x : selectedResidueField (localSeparableValuationSubring K)` | a point of the residue field `Ω` of `B` |

### The two sides

- Left side. `localSeparableResidueAlgAction K` is a continuous monoid
  homomorphism from `Gal(SeparableClosure K/K)` to the automorphisms of `Ω`
  over the base residue field `decompositionResidueField K B`. The term
  `localSeparableResidueAlgAction K sigma.1 x` applies the image of
  `sigma.1` to `x`, through Mathlib's coercions to functions.
- Right side. Write `E = abstractFixedField K (SeparableClosure K) H`.
  `abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma` is the
  element of `Gal(SeparableClosure K/E)` that corresponds to `sigma`; it
  has the same underlying map of `SeparableClosure K`.
  `residueAlgActionOfEqTop E B h` is the residue action of the whole group
  `Gal(SeparableClosure K/E)` on `Ω`, by automorphisms over
  `decompositionResidueField E B`. Its argument `h` is the proof that the
  decomposition group of `B` over `E` is everything.

The proof term `h` is `localAbstractFixedDecompositionGroup_eq_top K H`, as
in the source. In the Library this name is the published M250.005 proof of
the closed proposition `localAbstractFixedDecompositionGroup_eq_topStatement`,
and the term is that proof applied to `K` and `H`. Its type is
`decompositionGroup E B = ⊤`, the source type.

Both sides are elements of the same type `selectedResidueField B`, so the
equation compares two points of `Ω`. The two automorphisms of `Ω` live over
different base fields (`decompositionResidueField K B` and
`decompositionResidueField E B`), and the statement compares only their
values.

`residueAlgActionOfEqTop` needs `[IsGalois E (SeparableClosure K)]`.
Instance search finds it as Mathlib's `IsGalois.tower_top_intermediateField`
applied to Mathlib's `separableClosure.isGalois`, the Galois instance of
`SeparableClosure K` over `K` (a private probe printed the synthesized
term). The field and algebra
structures on `E` are Mathlib's instances for an `IntermediateField`.

### Binders and scope

The source theorem has no `omit` or `include` line before it. Its signature
mentions `K`, and through `localSeparableResidueAlgAction K` all four
instance variables. So the source theorem takes exactly the section
variables of lines 33–34, followed by its own binders, and the proposition
binds exactly these. A private probe confirmed it: a theorem with the source
signature, declared under the same section variables, has by `#check` the
type `∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K] (H : ClosedSubgroup Gal(SeparableClosure K/K))
(sigma : ↥H.toSubgroup) (x : selectedResidueField (localSeparableValuationSubring K)), ...`.

The source file also declares three local instances (M250.002–M250.004,
lines 57–78) for the intermediate field of M250.001. The statement does not
mention that intermediate field, so they are not used and are omitted.

## Published declarations used

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M249.020, `LocalClassFieldTheory.localSeparableResidueAlgAction` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction` ([definition](../../LocalResidueDatum/U020/Definitions.md)) |
| M244.003, `LocalClassFieldTheory.residueAlgActionOfEqTop` | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop` ([definition](../../ResidueActionIndex/U003/Definitions.md)) |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` ([definition](../../FiniteAbstractFixedField/Initial/Definitions.md)) |
| M099.007, `LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup` | `Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup` (same module as M099.001) |
| M250.005, `LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_top` | `Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_top` ([proof](../U005/Proofs.md) of the [target](../U005/Statements.md)) |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (imported through the M249.020 and M250.005 modules) |
| M243.004, `RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField` (imported through the M249.020 module) |

- `abstractFixedField k Ω H` abbreviates Mathlib's
  `IntermediateField.fixedField H.toSubgroup`, the subfield fixed by `H`.
- `abstractSubgroupEquivGaloisGroup k Ω H` is the group isomorphism
  `H.toSubgroup ≃* Gal(Ω/abstractFixedField k Ω H)` obtained from Mathlib's
  `InfiniteGalois.fixingSubgroup_fixedField` and
  `IntermediateField.fixingSubgroupEquiv`. It does not change the underlying
  automorphism of `Ω`.
- `residueAlgActionOfEqTop K A hA` is the residue action
  `decompositionGroupResidueAction` (M243.024) of the decomposition group,
  composed with the
  identification `toDecompositionGroupOfEqTop K A hA` (M244.001) of the
  whole Galois group with the decomposition group when `hA` says that they
  are equal.
- `localSeparableResidueAlgAction K` has underlying monoid homomorphism
  `residueAlgActionOfEqTop K B (localSeparableDecompositionGroup_eq_top K)`
  (M249.010 for the proof argument).

`ClosedSubgroup`, `Gal(_/_)`, `SeparableClosure`, `IntermediateField`,
`ValuativeRel` and `IsNonarchimedeanLocalField` are Mathlib declarations.
The opened namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring` is
the adapted form of the source `open HilbertRamification.ValuationSubring`
(line 30); it lets the statement write `selectedResidueField` as in the
source.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), against Library
commit `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22`, compiled the module with
no errors or warnings (diagnostic `28aa03f7-3263-45b8-8409-156a582340ff`).

A private probe compiled against this module proves the target with the
source proof (lines 112–123) after `intro K _ _ _ _ H sigma x`. That proof
writes `x` as the residue class of some `a ∈ B`, rewrites both sides with
`change` to the residue classes of the actions of the two decomposition-group
elements on `a`, and closes the goal by `congr 1`. This shows that the target
is the intended proposition and that its proof needs no other unpublished
result. The probe is development evidence only; the proof is a separate
unit and is not part of this module.

## Relation to other Library and Mathlib declarations

The whole Library at commit `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22` was
searched for `localSeparableResidueAlgAction` and `residueAlgActionOfEqTop`.
They occur only in the M244.003 definition, the M244.004 statement
`residueAlgActionOfEqTop_surjectiveStatement`, the M249.019 statement and
proof (continuity of the action), the M249.020 definition and the M249.021
statement `localSeparableResidueAlgAction_surjectiveStatement`. None of
them relates the action over `K` to the action over the fixed field of a
subgroup, which is what this proposition does. The thirteen Library files
that use `abstractSubgroupEquivGaloisGroup` (under
`FiniteAbstractFixedField`, `FixedFieldRelativeNorm` and
`FixedFieldIntrinsicReciprocity`) do not mention residue fields at all.
Mathlib has no declaration about `selectedResidueField`, which is a Library
definition.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean#L99-L123)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The complete
file was read and has SHA-256
`84865498b7b4788c2ebeecb92aeaca7a1bb9a62e2005cb1554386e2a52bf674a`, the value
recorded for M250 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m250).

| Partition unit | Original declaration in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M250.006 | theorem `localAbstractFixedResidueAction_apply` | 99–111 (proof 112–123) | `localAbstractFixedResidueAction_applyStatement` |
| Same source theorem, later proof phase | | | `localAbstractFixedResidueAction_apply`, reserved for the proof |

Lines 99–101 are the doc comment, line 102 the theorem name, lines 103–105
its binders and lines 106–111 its type; the proof occupies lines 112–123.
The header occupies lines 1–5 and the imports lines 7–8. The source module
opens namespace `LocalClassFieldTheory` (line 20), opens `CyclicCohomology`,
`RamificationTheory` and `ClassFormation` (line 21), `LocalFieldTheory`
(line 23), `scoped Pointwise ValuativeRel` (line 29),
`HilbertRamification.ValuationSubring` (line 30) and
`Field.absoluteGaloisGroup` (line 31), works in `noncomputable section`
(line 27) and declares the section variables at lines 33–34.

Worker 85 made these changes on 15 November 2026:

- added the `Langlands.NYLL` prefix to the namespace and to the opened
  namespace, which becomes
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`;
- packaged the theorem type as a closed proposition, a `def` with the suffix
  `Statement`. The section variables become the leading `∀`-binders, with
  the same kinds (explicit for `K`, instance-implicit for the rest),
  followed by the explicit binders `H`, `sigma` and `x`. The type after the
  binders is the source type unchanged; its subterm
  `localAbstractFixedDecompositionGroup_eq_top K H` now denotes the
  published M250.005 proof applied to `K` and `H`. The declaration doc
  comment states that the definition states the source theorem and keeps
  the source doc comment;
- omitted the proof, the `noncomputable section`, the other `open` lines,
  the local instances and all other declarations;
- replaced the source imports by the published modules
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U005.Proofs`
  (M250.005, which also brings in `abstractFixedField`,
  `abstractSubgroupEquivGaloisGroup` and `localSeparableValuationSubring`),
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions`
  (M249.020) and
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions`
  (M244.003);
- wrote a new short module docstring for this unit.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M250.006 statement target. Its proof and the
other rows of the source file are not part of this unit.
