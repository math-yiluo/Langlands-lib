# The two residue-kernel characterizations

This module proves both published closed targets for NYLL M160.017 and
M160.018. Its only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelStatements`.
The actual algebra automorphisms, integer-ring restrictions, residue maps
and their published evaluation theorems are supplied by that import's
dependency chain. No published file is changed.

## Exact theorem interfaces

Both theorems are in `Langlands.NYLL.LocalFieldTheory`. Their complete,
unapplied types are exactly the following named propositions:

| Theorem | Complete type |
| --- | --- |
| `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq.{u}` | `GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffResidueEqStatement.{u}` |
| `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal.{u}` | `GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffSubMemMaximalIdealStatement.{u}` |

There are no mathematical parameters outside either proposition. Each has
the single arbitrary universe parameter `u`. Each published proposition
quantifies, internally and in this order,

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)),
```

Thus the same arbitrary universe is shared by the two fields, and all
seven supplied instance binders are retained. `Gal(L/K)` denotes
`L ≃ₐ[K] L`; it requires no `IsGalois` assumption. The valuation extension
provides the canonical integer-ring algebra induced by `algebraMap K L`.
The integral-closure instance concerns the actual integer ring of `L`
over the actual integer ring of `K` in `L`.

Writing the common kernel membership as
`σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker`,
the first theorem identifies it with

```lean
∀ x : 𝒪[L],
  IsLocalRing.residue 𝒪[L]
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) =
    IsLocalRing.residue 𝒪[L] x
```

The second identifies the same kernel membership with

```lean
∀ x : 𝒪[L],
  galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x ∈
    (𝓂[L] : Ideal 𝒪[L])
```

The conjugate residue remains on the left of the equality, and the
difference remains conjugate minus original. Both results are
equivalences. No algebraicity, finiteness, topology, completeness,
discreteness, local-field, finite-residue, preservation-certificate or
conclusion premise is introduced. The module adds no instance or helper
declaration.

## The concrete maps

The scoped notation `𝒪[F]` denotes
`Valuation.integer (ValuativeRel.valuation F)`. Its maximal ideal is
`𝓂[F] = IsLocalRing.maximalIdeal 𝒪[F]`, and its residue field is the
actual quotient
`𝓀[F] = IsLocalRing.ResidueField 𝒪[F] = 𝒪[F] ⧸ 𝓂[F]`.
`IsLocalRing.residue 𝒪[F]` is the quotient ring homomorphism.

The [published homomorphism](AlgebraDefinitions.md)
`galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L` has codomain
`𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]`. Its value at `σ` is, by its `toFun` field,
`galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ`. The latter's
underlying forward map is the
[published residue-field equivalence](Definitions.md)
`galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ`.
That equivalence is `IsLocalRing.ResidueField.mapEquiv` of the
[published integer-ring restriction](../GaloisIntegerRing/Definitions.md)
`galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ`.
These supplied maps and quotient/algebra structures are used throughout.

The restriction is built from Mathlib's `galRestrict'` and
`AlgEquiv.ofAlgHom`. Its ambient-field evaluation is given propositionally
by the published
`galoisGroupIntegerRingEquivOfIsIntegralClosure_apply`; no new
definitional evaluation of the restricted map is asserted here.
The proof below only needs the
[published residue-representative evaluation](Proofs.md)
`galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L σ x`.

## Implemented proofs

For M160.017, `MonoidHom.mem_ker` first rewrites membership in the actual
kernel to the equality of the image algebra automorphism with the identity.
In the forward direction, `congrArg` evaluates this equality at
`IsLocalRing.residue 𝒪[L] x`. A `change` exposes the forward map of the
published residue equivalence and the identity's value; these agree
definitionally with the two sides already present. Rewriting with the
published representative evaluation gives exactly the required equality
of residues.

Conversely, `AlgEquiv.ext` reduces the equality with the identity to
pointwise equality on the residue field. For any such point,
`IsLocalRing.residue_surjective` supplies an integer representative.
The same `change` and representative evaluation reduce the goal to the
assumed equality for that integer. This establishes both directions for
the whole quotient, not merely for selected representatives.

For M160.018, rewriting with the first theorem reduces the claim to an
equivalence between two universally quantified conditions on integers.
`forall_congr'` reduces this to one integer `x`. The three rewrites

```lean
rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
```

first express equality of the two residue classes as their difference
being zero, then express that difference as the residue of the conjugate
difference, and finally identify zero residue with membership in the
actual maximal ideal. This proves the equivalence in the required
subtraction orientation.

## Original source and modifications

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean#L247-L303)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its full-file
SHA-256 is
`b3c47318364659eb1a14b872f8462a2284f47125b1d84391c5c93a3ba87f2c67`.
The pinned local original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The ambient definitions at lines 1–113 and both proof passages at
247–303 were read, and the file hash was verified.

| Source unit | Source theorem in `LocalFieldTheory` | Source lines | Adapted theorem |
| --- | --- | --- | --- |
| M160.017 | `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq` | 247–273, theorem at 249 | Same spelling in `Langlands.NYLL.LocalFieldTheory` |
| M160.018 | `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal` | 275–303, theorem at 277 | Same spelling in `Langlands.NYLL.LocalFieldTheory` |

Worker 84 made the following adaptations on 29 October 2026:

- added the `Langlands.NYLL` namespace prefix, replaced the broad source
  imports with the single published target import, and rewrote the
  comments for this focused proof unit;
- stated each theorem with its exact published closed proposition as
  its complete type, then introduced all original parameters and
  instances within the proof;
- made the kernel-equality rewrite explicit with `MonoidHom.mem_ker`;
- replaced the source M160.007 application alias and its simplifier use
  by definitional `change` steps exposing the published homomorphism's
  actual forward map, followed by explicit applications of the published
  closed-target residue evaluation;
- used `IsLocalRing.residue_surjective` instead of the source's
  `Ideal.Quotient.mk_surjective`, and used that published evaluation
  explicitly in the reverse direction as well;
- replaced the second source proof's separate forward/reverse arguments
  by `forall_congr'` and the three quotient rewrites described above.

The source route for the first proof is retained. The second is shortened
using the same residue-zero and subtraction facts. No implementation
draft from another worker was reused; Worker 106 supplied the task and
proof-route suggestions, without adapted Lean code. Existing Library
and Mathlib results are reused by import and declaration name.

The [public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m160)
records no patch10 change to this module. No patch10 code is used. This
unit exports only M160.017/.018 proofs. It introduces no M160.007 alias,
stabilizer or inertia data, kernel-cardinality or ramification result,
filtered reciprocity theorem, or host reciprocity comparison.

## Provenance and license

The original is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable errata directory was present in the project or current
Library notes on 29 October 2026.

The Lean file preserves the original copyright/license/author header
verbatim: copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged. Their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development checks

Both complete unapplied theorem declarations were separately inspected
with `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, using Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The residue-equality diagnostic
is `1e9dfeac-360c-417c-91ac-9541a37cdd95`; the maximal-ideal diagnostic is
`4ea3be85-3b32-4da0-b18d-970405836a22`. Each returned successful Lake
compilation, zero errors or warnings, kind `theorem`, exactly `[u]` as
its universe list, and only `propext`, `Classical.choice` and `Quot.sound`
as transitive axioms. The module also passed the incremental development
check `a635b685-d0ee-49ad-a416-ecf34bbb056d`.

These are development checks. Each theorem is submitted in its own proof
record bound to its own published statement; official exact-target
validation, independent semantic acceptance and publication are separate
requirements.
