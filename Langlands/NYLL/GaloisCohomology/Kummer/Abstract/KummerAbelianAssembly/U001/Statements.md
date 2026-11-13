# NYLL M022.001: extension-subgroup membership target

The paired file defines
`Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iffStatement`, the exact
proposition of NYLL source unit M022.001 after expanding the extension-subgroup
abbreviation. It says that membership in `G_L`, viewed inside `G_K`, is
ambient membership in `G_L`. This contribution supplies the proposition;
it does not publish its proof.

## Source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`,
SHA-256 `ca4ad38a7ed46fa029400e2c7718faf0587b4206731c82c8c45d6839b719f54c`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registration is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project errata notes.

| Source | Adaptation |
| --- | --- |
| M022.001, `KummerTheory.mem_extensionSubgroup_iff`, docstring lines 30–31, `@[simp]` at 32, theorem lines 33–38 | `Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iffStatement` |
| M004.002, `CyclicCohomology.extensionSubgroup`, `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54, declaration at 51 | Mathlib expression `L.toSubgroup.subgroupOf K.toSubgroup` |

The second source file has SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
Its abbreviation is exactly the displayed Mathlib expression; the containment
proof does not occur in its body. The task explicitly directs this expansion.
The current Library also publishes the same abbreviation as
`Langlands.NYLL.CyclicCohomology.extensionSubgroup`, which is used in the
private source-comparison check, but is not imported by this focused target.

## Full statement and telescope

```lean
def Langlands.NYLL.KummerTheory.mem_extensionSubgroup_iffStatement
    {G : Type u} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (k : K.toSubgroup) : Prop :=
  k ∈ L.toSubgroup.subgroupOf K.toSubgroup ↔ (k : G) ∈ L
```

`G` is implicit and has an arbitrary universe `u`. The group and topology
arguments are instance-implicit. `K`, `L`, `hLK` and `k` are explicit, in that
order. The containment proof `hLK` is retained even though expanding the
abbreviation makes its absence from the proposition explicit.

The source's section context is `namespace KummerTheory` at line 20,
`open CyclicCohomology` at 22, `noncomputable section` at 26 and
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at 28.
This theorem's own `{G : Type*}` at line 34 shadows that section variable.
Thus the source theorem and this target both have one universe parameter;
the theorem is not restricted to universe-zero groups. No topological-group,
normality, finiteness or representation hypothesis belongs to this unit.

Mathlib's `Subgroup.mem_subgroupOf`, instantiated with `H := L.toSubgroup`
and `K := K.toSubgroup`, has the same conclusion. Its RHS membership is
definitionally membership in `L`. A focused private check applies that
theorem under the entire source telescope, retaining `hLK`. The published
target still has the exact required NYLL name and complete telescope.

## Modifications by Worker 291

1. Extract only M022.001. Replace `namespace KummerTheory` by
   `namespace Langlands.NYLL.KummerTheory`.
2. Replace the theorem by a `def` returning `Prop`, append `Statement`, and
   use its original conclusion as the body. Remove the source proof
   `Iff.rfl` and the theorem's `@[simp]` attribute. The declaration docstring
   is shortened to describe a target.
3. Expand `extensionSubgroup (G := G) K L hLK` to
   `L.toSubgroup.subgroupOf K.toSubgroup`. Keep every original binder and
   binder kind, including `hLK`, and the original arbitrary group universe.
4. Replace the source imports
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors` and
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerFixedField` by
   `Mathlib.Topology.Algebra.Group.ClosedSubgroup`, which supplies the
   closed-subgroup interface and imports the subgroup construction.
   Drop the unused `open CyclicCohomology` and the shadowed section
   variable; keep `noncomputable section`. Replace the module docstring
   with the focused description and modification record.

No data, additional assumptions, instances or axioms are introduced.
M022.002–006 are outside this file. This target asserts no host
class-formation, cup-product, Tate, transfer or reciprocity result.

## Verification

Worker 291 checked the focused module in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation and declaration
inspection succeed; inspection reports a definition with one level parameter
`u_1` and `statement_returns_prop: true`. Its only axioms are `propext` and
`Quot.sound`. Compilation emits one unused-variable warning for the
deliberately retained source binder `hLK`.

A private probe copies the source telescope and proposition using the
published `extensionSubgroup` abbreviation and checks by `rfl` that its
complete unapplied predicate equals this predicate at an arbitrary universe.
A separate unapplied assignment checks the full expected telescope, and
`#print` confirms the universe and binder kinds above. The probe also checks
the correspondence with `Subgroup.mem_subgroupOf`. These are development
checks; independent semantic acceptance and publication remain separate.

## Attribution

The original copyright, Apache-2.0 release and author header are preserved
verbatim: copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The retained files are
[`licenses/NYLL/LICENSE`](../../../../../../../licenses/NYLL/LICENSE),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and [`licenses/NYLL/NOTICE`](../../../../../../../licenses/NYLL/NOTICE),
SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The port inventory records no patch10 modification for M022. No patch10 code
or unpublished draft was reused.
