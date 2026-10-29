# Residue-kernel characterization targets

This module states the two kernel characterizations from NYLL source units
M160.017 and M160.018 as closed proposition definitions. It proves neither
formula. Both declarations belong to `Langlands.NYLL.LocalFieldTheory`;
their complete unapplied types are `Prop`, with a single arbitrary universe
parameter `u` and no mathematical declaration parameters.

## The two statements

Each definition quantifies the following arguments inside its proposition,
in exactly this order:

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)),
```

The body of
`GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffResidueEqStatement`
is exactly

```lean
σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
  ∀ x : 𝒪[L],
    IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) =
      IsLocalRing.residue 𝒪[L] x
```

It says that the induced residue algebra automorphism is the identity
exactly when the integer-ring restriction preserves the residue of every
integer. The residue of the conjugate is on the left of the equality.

The body of
`GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffSubMemMaximalIdealStatement`
is exactly

```lean
σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
  ∀ x : 𝒪[L],
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x ∈
      (𝓂[L] : Ideal 𝒪[L])
```

It says that the same kernel membership is equivalent to the difference
of each conjugate and the original integer lying in the maximal ideal.
The subtraction is the conjugate minus the original integer, in `𝒪[L]`.
Both conclusions are equivalences for the actual kernel, not subgroup
inclusions or a condition on an abstract supplied action.

## Hypotheses, notation and imported maps

The universe `u` is arbitrary and shared by `K` and `L`, as in the source.
`Gal(L/K)` is Mathlib's `L ≃ₐ[K] L`, the group of automorphisms of the
supplied `K`-algebra. This notation imposes no `IsGalois` hypothesis.
Both field structures, both valuative relations, and `Algebra K L` are
the supplied structures.

The `Valuation.HasExtension` instance relates the canonical valuation of
`K` to the pullback of the canonical valuation of `L`. It provides the
usual integer-ring algebra induced by `algebraMap K L`.
`IsIntegralClosure 𝒪[L] 𝒪[K] L` says that the actual integer ring of `L`,
embedded in `L`, is the integral closure of the integer ring of `K`.
All seven instance binders are retained in their original order.

The scoped `ValuativeRel` notation denotes the concrete objects:

| Notation | Object |
| --- | --- |
| `𝒪[F]` | `Valuation.integer (ValuativeRel.valuation F)`, the subtype of field elements with valuation at most one |
| `𝓂[F]` | `IsLocalRing.maximalIdeal 𝒪[F]` |
| `𝓀[F]` | `IsLocalRing.ResidueField 𝒪[F]`, the quotient `𝒪[F] ⧸ 𝓂[F]` |
| `IsLocalRing.residue 𝒪[F]` | The actual quotient ring homomorphism to `𝓀[F]` |

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.AlgebraDefinitions`.
Its published
[`galoisGroupResidueAlgEquivHomOfIsIntegralClosure`](AlgebraDefinitions.md)
has type

```lean
Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])
```

under the same hypotheses. Its value at `σ` is the published
`galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ`. Its underlying
residue map is
[`galoisGroupResidueFieldEquivOfIsIntegralClosure`](Definitions.md),
which is Mathlib's `IsLocalRing.ResidueField.mapEquiv` of the published
[`galoisGroupIntegerRingEquivOfIsIntegralClosure`](../GaloisIntegerRing/Definitions.md).
Thus all the maps and quotient structures in the targets are the existing
ones; no valuation, scalar structure or quotient is replaced.

The imported [integer-ring evaluation](../GaloisIntegerRing/Proofs.md)
identifies the ambient value of the restricted image of `x` with
`σ (x : L)`. The published restriction is built with Mathlib's
`galRestrict'` and `AlgEquiv.ofAlgHom`, using `IsIntegralClosure.equiv`.
This ambient evaluation is propositional, supplied by
`galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` and Mathlib's
`algebraMap_galRestrict'_apply`; it is not asserted to hold by `rfl`.
The [residue evaluation](Proofs.md) identifies the image of a residue
representative with the residue of its restricted image. These interfaces
explain the concrete meaning of the targets; this module contains no
proof using them.

No algebraicity, finite-dimensionality, `IsGalois`, completeness, topology,
local-field, discreteness, finite-residue-field, prime, integer-preservation,
action-certificate or conclusion premise is added. The module declares no
instance. It does not modify any published `ResidueGalois` or
`GaloisIntegerRing` pair.

## Original source and correspondence

The source is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean#L247-L303)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its full-file SHA-256
is `b3c47318364659eb1a14b872f8462a2284f47125b1d84391c5c93a3ba87f2c67`.
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Lines 1–113 and 247–303, including the map definitions and both original
proofs, were read and the file hash verified.

| Source unit and theorem in `LocalFieldTheory` | Source lines | Closed target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- |
| M160.017: `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_residue_eq` | 247–273; theorem starts 249 | `GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffResidueEqStatement` |
| M160.018: `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal` | 275–303; theorem starts 277 | `GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffSubMemMaximalIdealStatement` |

The source unit identifiers are recorded in the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m160).
The source M160.017 proof evaluates a kernel equality on residue
representatives in one direction and uses surjectivity of the quotient map
and algebra-equivalence extensionality in the other. M160.018 rewrites by
M160.017 and uses that the quotient map sends a difference to zero exactly
when that difference belongs to the maximal ideal. Those original proof
bodies are not ported here.

Worker 84 made these changes on 29 October 2026:

- added the `Langlands.NYLL` namespace prefix and used the published
  prefixed maps;
- renamed each source theorem type to the exact PascalCase target above
  and made it a `def ... : Prop`;
- moved every source parameter and instance into the proposition,
  preserving their order, the single shared universe, both equivalences
  and the equality and subtraction orientations;
- omitted both proof bodies, replaced the source imports with the
  published algebra-definition module, and rewrote the comments for
  statement scope.

No implementation or proof draft from another worker was used. Existing
Library and Mathlib mathematics is reused by import and declaration name.
The unit introduces no M160.007 evaluation alias, M160.009–.016
action/stabilizer/inertia data, later kernel-cardinality statement, M328
ramification result or host reciprocity result. Proofs of these two targets
remain separate work.

## Provenance and license

The original is in registration
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable errata file was found in project or current Library notes
on 29 October 2026. The public partition records no patch10 change to this
source module; no patch10 code is reused.

The Lean file retains the original copyright and author header verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.


## Development checks

Both complete unapplied declarations were compiled and inspected with
`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
The terminal diagnostic records are `1373012b-8b61-431c-bf0d-2260a7c211e7`
for the residue-equality target and `e0693923-102b-47fe-be32-4d9fced49bc1`
for the maximal-ideal target. Each reported `ok: true`, no errors or
warnings, kind `definition`, `statement_returns_prop: true`, and exactly
`[u]` as its universe parameters. Their complete types are `Prop`, with the same
32-byte expression fingerprint
`7eb9c843b0fd71b8fd2d1fabbb34bb5e51c5767a961a5fe1323fb9a277b48cde`.
Only `propext`, `Classical.choice` and `Quot.sound` occur in their transitive
axiom sets. These are author checks; independent semantic review and
publication validation remain separate requirements.
