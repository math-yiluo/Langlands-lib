# NYLL M022.002: quotient-action evaluation target

The paired file defines
`Langlands.NYLL.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_valStatement`,
the proposition of NYLL source unit M022.002. On the actual invariant
subtype, the quotient action at the class of `k` has ambient value
`A.ρ k.1 a.1`. This contribution supplies the target and reuses the published
construction; it does not publish the target's proof.

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
| M022.002, `KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val`, docstring lines 40–41, `@[simp]` at 42, theorem lines 43–51 | `Langlands.NYLL.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_valStatement` |
| M002.001, `IntegralRepGroupType`, `Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean`, line 18 | Published `Langlands.NYLL.IntegralRepGroupType`, unchanged abbreviation for `Type 0` |
| M004.002, `CyclicCohomology.extensionSubgroup`, `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54, declaration at 51 | Mathlib expression `M.toSubgroup.subgroupOf K.toSubgroup` |
| M004.003, `CyclicCohomology.extensionFixedRepresentation`, same file, lines 56–68, declaration at 61 | Published `Langlands.NYLL.CyclicCohomology.extensionFixedRepresentation` |

The M004 source file has SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
The abbreviation is exactly the displayed Mathlib expression. Its
containment argument does not occur in the body. The task explicitly
directs its expansion; the current Library also publishes the same
abbreviation, used in the private source-comparison check.

## Full statement and telescope

Writing `extensionFixedRepresentation` for the published
`Langlands.NYLL.CyclicCohomology.extensionFixedRepresentation`, the target is:

```lean
def Langlands.NYLL.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_valStatement
    {G : Langlands.NYLL.IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep.{0} ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (k : K.toSubgroup) : Prop :=
  ((extensionFixedRepresentation A K M hMK hnormal).ρ
    ((QuotientGroup.mk' (M.toSubgroup.subgroupOf K.toSubgroup)) k) a).1 =
    A.ρ k.1 a.1
```

The source's section context is `namespace KummerTheory` at line 20,
`open CyclicCohomology` at 22, `noncomputable section` at 26 and
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at 28.
These are kept within the prefixed namespace. The group `G` is implicit
and in universe zero; group and topology instances follow. Next come
explicit `A`, `K`, `M` and `hMK`, instance-implicit `[hnormal]`, explicit
`a`, then explicit `k`. The source writes `A : Rep ℤ G` without an annotation,
as does the paired Lean file. The reused construction constrains it to
`Rep.{0} ℤ G`, so the elaborated declaration has no universe parameters.
The representation's carrier is also in universe zero.

Although this statement's normality argument is instance-implicit, it is
passed explicitly as the final argument of `extensionFixedRepresentation`,
whose own normality argument is explicit. Both binder kinds match their
respective sources. No topological-group, continuity, finiteness, cyclicity
or commutativity assumption is present.

The representation is the actual Mathlib construction
`Rep.quotientToInvariants (Rep.res K.toSubgroup.subtype A)
  (M.toSubgroup.subgroupOf K.toSubgroup)`.
Its carrier is the subtype of `A.V` fixed by `M` as a subgroup of `K`, and
the quotient `K ⧸ M` acts on that subtype. The equation compares the
underlying ambient vector of the quotient action with the original action
of the representative. It does not replace the subtype or action by
supplied data or an abstract compatibility premise.

## Modifications by Worker 291

1. Extract only M022.002 and its section context. Prefix the source namespace
   with `Langlands.NYLL`; `open CyclicCohomology` now resolves to the
   published NYLL namespace.
2. Replace the theorem by a `def` returning `Prop`, append `Statement`, and
   use the original equality as the body. Remove the source proof `rfl` and
   the theorem's `@[simp]` attribute. Shorten the declaration docstring to
   describe a target.
3. Expand each written occurrence of
   `extensionSubgroup (G := G) K M hMK` to
   `M.toSubgroup.subgroupOf K.toSubgroup`, in both the normality premise and
   the quotient map. The subgroup inside the published representation is
   definitionally the same term. Keep all parameters, their order, their
   binder kinds and all actual objects.
4. Replace the source imports
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors` and
   `Nyll.GaloisCohomology.Kummer.Abstract.KummerFixedField` by
   `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`.
   They provide the unchanged group-universe alias and actual extension
   fixed representation. M022.001 is not a dependency of this proposition.
   Replace the module docstring with the focused description and modification
   record.

No new construction, instance or axiom is introduced. M022.001 and
M022.003–006 are outside this file. This target asserts no host
class-formation, cup-product, Tate, transfer or reciprocity result.

## Verification

Worker 291 checked the focused module in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation succeeds without
errors or warnings. Declaration inspection reports a definition with no
universe parameters and `statement_returns_prop: true`. Its only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

A private probe copies the complete source telescope and equality using the
published `extensionSubgroup` abbreviation, and checks by `rfl` that its
complete unapplied predicate equals this predicate. A separate unapplied
assignment checks the full expected telescope with `A : Rep.{0} ℤ G`;
`#print` confirms the implicit group, instance binders, explicit arguments
and universe-zero representation. These checks cover the normality premise,
invariant subtype, quotient map and both sides of the equality. They are
development checks; independent semantic acceptance and publication remain
separate.

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
