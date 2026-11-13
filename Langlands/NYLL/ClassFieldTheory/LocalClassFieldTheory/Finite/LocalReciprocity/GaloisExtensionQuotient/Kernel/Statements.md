# Base-fixing extension subgroup and quotient-kernel targets

Adapted by Worker 4913 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`
(SHA-256 `1f823480006ba2691c249c7e1f01f63300871f8c94ab6954be9105f913d4c831`).
The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and the
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M089.003 | theorem `extensionSubgroup_base_eq_subgroupOf` (docstring 49–50, signature 51–57, proof 58) | `extensionSubgroup_base_eq_subgroupOfStatement` |
| M089.007 | theorem `baseFixingToAmbientQuotient_ker` (docstring 86–87, signature 88–93, proof 94–99) | `baseFixingToAmbientQuotient_kerStatement` |

Every unqualified original name is in the source namespace
`LocalClassFieldTheory`; every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`. Each adapted declaration is a `def`
returning `Prop` whose body is the source theorem statement. Neither has a
proof here; the proofs are separate tasks, which may use the source theorem
names `extensionSubgroup_base_eq_subgroupOf` and
`baseFixingToAmbientQuotient_ker` in the same namespace.

## Parameters

Both definitions take the source section variables of line 29,

```lean
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
```

followed by the source theorem binders: `(E : IntermediateField K Ω)` for
M089.003, and `(E : IntermediateField K Ω) [IsGalois K E]` for M089.007. Both
fields are in `Type` (universe zero), as in the source. Both definitions use
`[IsGalois K Ω]` through `closedFixingSubgroup`, so Lean keeps it, as it does
for the source theorems. The resulting telescopes, checked with `#check`, are

```lean
extensionSubgroup_base_eq_subgroupOfStatement :
  (K Ω : Type) → [Field K] → [Field Ω] → [Algebra K Ω] → [IsGalois K Ω] →
    IntermediateField K Ω → Prop
baseFixingToAmbientQuotient_kerStatement :
  (K Ω : Type) → [Field K] → [Field Ω] → [Algebra K Ω] → [IsGalois K Ω] →
    (E : IntermediateField K Ω) → [IsGalois K ↥E] → Prop
```

## The two propositions

Write `G₀ = closedFixingSubgroup K Ω ⊥` for the closed subgroup of
`Gal(Ω/K)` fixing the bottom intermediate field (as a set, all of
`Gal(Ω/K)`), and `G_E = closedFixingSubgroup K Ω E` for the closed subgroup
fixing `E`. The inclusion proof `fixingSubgroupLeBase K Ω E : G_E ≤ G₀` is the
published M089.002 theorem.

`extensionSubgroup_base_eq_subgroupOfStatement K Ω E` is the source statement

```lean
extensionSubgroup G₀ G_E (fixingSubgroupLeBase K Ω E) =
  G_E.toSubgroup.subgroupOf G₀.toSubgroup
```

So the class-formation extension subgroup attached to `G_E ≤ G₀` is `G_E`
viewed as a subgroup of the group `G₀`. Since the published
`extensionSubgroup` is an abbreviation for exactly this `subgroupOf`, the
proposition holds by `rfl`, which is also the source proof. It is stated here
only because the task requires each source theorem as a separate target.

`baseFixingToAmbientQuotient_kerStatement K Ω E` is the source statement

```lean
(baseFixingToAmbientQuotient K Ω E).ker =
  extensionSubgroup G₀ G_E (fixingSubgroupLeBase K Ω E)
```

The published map `baseFixingToAmbientQuotient K Ω E` (M089.006) is the
composite of the inclusion `G₀ → Gal(Ω/K)` with the quotient map
`Gal(Ω/K) → Gal(Ω/K) ⧸ G_E`; the hypothesis `[IsGalois K E]` makes `G_E`
normal, so the quotient is a group. The proposition says that its kernel is
`G_E` viewed inside `G₀`.

## Library declarations used

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`, imported through the next two modules) |
| M089.002, `LocalClassFieldTheory.fixingSubgroupLeBase` | `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs`) |
| M089.006, `LocalClassFieldTheory.baseFixingToAmbientQuotient` | `Langlands.NYLL.LocalClassFieldTheory.baseFixingToAmbientQuotient` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Definitions`) |

The published `extensionSubgroup` is the source abbreviation itself, so it is
used here directly rather than replaced by its `subgroupOf` body. The
published `fixingSubgroupLeBase K Ω E` has the type
`fixingSubgroupLeBaseStatement K Ω E`, which unfolds to the source inclusion
`(closedFixingSubgroup K Ω E).toSubgroup ≤ (closedFixingSubgroup K Ω ⊥).toSubgroup`.
It occurs only as the proof argument of `extensionSubgroup`, which ignores it.

## Modifications and attribution

Worker 4913 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued `def` with the `Statement` suffix,
  keeping the source section variables, the theorem binders in source order
  and the statement text. The proofs are omitted.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source `open RamificationTheory CyclicCohomology` (line 21) is kept;
  the unused `open ClassFormation` (line 23) is omitted. The
  `noncomputable section` of line 27 is kept.
- The M089.007 docstring "The kernel of the preceding map" becomes "The
  kernel of the base-to-ambient quotient map", since the preceding source
  definition (M089.006) is published in another module. The M089.003
  docstring is unchanged.
- The source imports (lines 7–8) are replaced by the published modules
  listed above. All other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and its module docstring records these modifications. The Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) retain the
original license and notices.

This unit contains only the M089.003 and M089.007 statement targets. It
makes no claim to discharge the host class-formation, cup, transfer, Tate or
reciprocity targets.
