# Normality targets for the extension subgroups of finite Galois realizations

Adapted by Worker 4913 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`
(SHA-256 `c3681d1d4a2363fb2b1a28fb984b458e8051e97c30c3d4ec66bc43608b1f44b2`).
The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and the
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M090.006 | instance `finiteGaloisExtensionSubgroupOfEmbedding_normal` (docstring 71–72, declaration 73–89) | Prop-valued `abbrev finiteGaloisExtensionSubgroupOfEmbedding_normalStatement` |
| M090.016 | instance `finiteGaloisExtensionSubgroup_normal` (docstring 199, declaration 200–215) | Prop-valued `abbrev finiteGaloisExtensionSubgroup_normalStatement` |

Every unqualified original name is in the source namespace
`LocalClassFieldTheory`; every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`.

## Why the instances are published as statement targets

Both source declarations are instances of the class `Subgroup.Normal`, which
is a proposition. Lean therefore compiles each of them as a theorem with the
instance attribute: they carry no data and their bodies are proofs. Following
the project rule that theorem targets are published as Prop-valued
definitions with separate proofs, this module publishes only the asserted
types. The source `change`/`infer_instance` proofs and the registration of
instances under the source names `finiteGaloisExtensionSubgroupOfEmbedding_normal`
and `finiteGaloisExtensionSubgroup_normal` are left to a later proof. This
module registers no instance, global, scoped or local.

The targets are reducible (`abbrev`), so a proof may be declared directly as
an instance whose type is the target applied to its arguments: instance
search unfolds the abbreviation to the `Subgroup.Normal` application. A
private check (not part of this submission) declares such an instance with
the source `change`/`infer_instance` body and compiles without errors.

## Parameters

The source section variables (lines 32–33) are

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
```

Like every definition-like declaration, each source instance keeps only the
section variables used by its type or body. Neither instance uses
`[FiniteDimensional K L]`. Both use `[IsGalois K L]`, through the Galois
instances M090.003 and M090.013 for the field ranges that their proofs need.
The source declarations therefore have the telescopes

```lean
finiteGaloisExtensionSubgroupOfEmbedding_normal :
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K), (extensionSubgroup ...).Normal
finiteGaloisExtensionSubgroup_normal :
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    (extensionSubgroup ...).Normal
```

with `K` and `L` in `Type` (universe zero). The targets state exactly these
binders, as explicit parameters in the same order and with the same binder
kinds. `[IsGalois K L]` does not occur in the target types, but it is a
binder of the source declarations, so it is kept. Explicit binders replace
the section variables because a definition would otherwise drop the unused
`[IsGalois K L]`.

These telescopes were confirmed by compiling the port of the source
instances with the source section variables. That port has the source types
and the source `change`/`infer_instance` bodies, and `#check` printed the
telescopes above. A private check compiles the targets together with that
port. It confirms by `rfl` that each target is the port's instance type
under the same binders, and that each ported instance proves the
corresponding target.

## The two targets

Write `G₀ = closedFixingSubgroup K (SeparableClosure K) ⊥`, the closed
subgroup of `Gal(SeparableClosure K / K)` fixing the bottom intermediate
field. For a `K`-embedding `i : L →ₐ[K] SeparableClosure K`, the published
`finiteGaloisFieldRangeOfEmbedding K L i` (M090.001) is the image `i(L)`, and
`finiteGaloisClosedFixingSubgroupOfEmbedding K L i` (M090.005) is
`closedFixingSubgroup K (SeparableClosure K) (i(L))`. The M090.006 target is

```lean
(extensionSubgroup G₀ (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
  (fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i))).Normal
```

that is, the fixing subgroup of `i(L)`, viewed inside `G₀`, is a normal
subgroup of `G₀`. The M090.016 target is the same statement for the canonical
realization `finiteGaloisFieldRange K L` (M090.011) and its fixing subgroup
`finiteGaloisClosedFixingSubgroup K L` (M090.015). The canonical realization
uses the published separable embedding of `L` into `SeparableClosure K`.

Each target body is the source instance type, token for token after the
namespace prefix. Here `extensionSubgroup` is the published reducible
abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup` (M004.002), and the
third argument is the published proof `fixingSubgroupLeBase` (M089.002) that
the fixing subgroup of the range lies in `G₀`.

For the later proof, the source script still works with published
declarations only. `change` unfolds the realization's fixing subgroup to
`closedFixingSubgroup K (SeparableClosure K) (range)`. `infer_instance` then
finds Mathlib's `Subgroup.normal_subgroupOf`, the published M089.004 instance
`closedFixingSubgroup_normal` and the published Galois instance M090.003 or
M090.013. The source can also use its unpublished instance M089.005
`extensionSubgroupBase_normal`. Because the targets are propositions, the
choice of route does not matter.

## Library declarations used

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`, imported through the realization module) |
| M089.002, `LocalClassFieldTheory.fixingSubgroupLeBase` | `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs`) |
| M090.001, .005, .011, .015 | `finiteGaloisFieldRangeOfEmbedding`, `finiteGaloisClosedFixingSubgroupOfEmbedding`, `finiteGaloisFieldRange`, `finiteGaloisClosedFixingSubgroup` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Realization.Definitions`) |

## Modifications and attribution

Worker 4913 made these changes to the two source instances:

- Each instance is replaced by a Prop-valued `abbrev` with suffix
  `Statement`, whose body is the source instance type. The source proofs
  (`:= by` at the ends of lines 80 and 206, scripts on lines 81–89 and
  207–215) and the instance attributes are omitted and deferred to a later
  proof. Each docstring is the source docstring
  after the prefix "Target of the source instance `…`:", with its first
  letter lowercased.
- The source section variables (lines 32–33) are replaced by explicit
  binders. These are the binders that the source instances actually keep,
  so `[FiniteDimensional K L]` is omitted, as described above. The
  `noncomputable section` (line 30) is omitted because the module defines
  only propositions.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source `open RamificationTheory CyclicCohomology KummerTheory` (line
  26) keeps `RamificationTheory` and `CyclicCohomology` and omits the unused
  `KummerTheory`.
- The source imports (lines 7–10) are replaced by the published modules
  listed above. All other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and its module docstring records these modifications. The Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) retain the
original license and notices.

This module contains only the M090.006 and M090.016 targets. It proves
nothing and makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
