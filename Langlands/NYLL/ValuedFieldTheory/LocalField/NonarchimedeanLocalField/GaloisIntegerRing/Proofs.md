# Integer-ring restriction evaluations: proofs

This module proves the two published closed statement targets for NYLL
source units M139.003 and M139.004. They give the ambient-field values of
the published restriction
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure`
and of its inverse. Nothing else is exported.

## Theorems and their exact targets

| Theorem in `Langlands.NYLL.LocalFieldTheory` | Its complete type |
| --- | --- |
| `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply.{u}` | `GaloisGroupIntegerRingEquivOfIsIntegralClosureApplyStatement.{u}` |
| `galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply.{u}` | `GaloisGroupIntegerRingEquivOfIsIntegralClosureSymmApplyStatement.{u}` |

Each theorem has the one universe parameter `u`, no other declaration
parameters and no premises. Its type is the published proposition itself.
The [statement module](Statements.md) is unchanged, so every quantifier is
inside the target. For all `K L : Type u` with `Field` and `ValuativeRel`
instances, an `Algebra K L`, the
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
instance, the `IsIntegralClosure 𝒪[L] 𝒪[K] L` instance, every
`σ : Gal(L/K)` and every `x : 𝒪[L]`, the targets state:

- forward law: `((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x : 𝒪[L]) : L) = σ (x : L)`;
- inverse law: `(((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x : 𝒪[L]) : L) = σ.symm (x : L)`.

The left side of each law is the inclusion into `L` of an element of the
integer ring. The inverse law concerns `.symm` of the same ring
equivalence restricted from `σ`. It is not a claim about extending an
arbitrary automorphism of `𝒪[L]` to `L`.

Here `𝒪[F]` is `Valuation.integer (ValuativeRel.valuation F)`, and
`Gal(L/K)` is the group `L ≃ₐ[K] L` of `K`-algebra automorphisms; it
does not assume that `L/K` is Galois. The scalar structures are the
canonical ones also used by the definition. The map `𝒪[K] → 𝒪[L]` is
induced by `algebraMap K L`, and `algebraMap 𝒪[L] L` is the subtype
inclusion. This module adds no hypothesis and no instance.

## Implemented proofs

Each proof introduces `K`, `L`, the seven instances, `σ` and `x`, then
applies Mathlib's `algebraMap_galRestrict'_apply`. That lemma is in
`Mathlib.RingTheory.IntegralClosure.IntegralRestrict` at the pinned
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. It states that
`algebraMap B₂ L₂ (galRestrict' A B B₂ f y) = f (algebraMap B L y)`.
Both proofs take `A = 𝒪[K]` and `B = B₂ = 𝒪[L]`, with `L₂ = L`.

The published definition is
`(AlgEquiv.ofAlgHom f g _ _).toRingEquiv`. Here
`f = galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.toAlgHom`, and
`g = galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.symm.toAlgHom`.

- Forward law: the lemma is applied to `σ.toAlgHom` and `x`.
- Inverse law: the lemma is applied to `σ.symm.toAlgHom` and `x`.

In both cases `exact` closes the goal by definitional unfolding. The
forward function of `AlgEquiv.ofAlgHom f g _ _`, and so of its ring
equivalence, is `f`. Its inverse function is `g`, which `RingEquiv.symm`
applies. `algebraMap 𝒪[L] L` is the subtype inclusion. Applying
`σ.toAlgHom` or `σ.symm.toAlgHom` to an element of `L` is applying
`σ` or `σ.symm`. No rewriting or `simp` call is needed.

The equalities hold propositionally, not by `rfl`. `galRestrict'` takes
the result through Mathlib's `IsIntegralClosure.equiv`, so no subtype
constructor exposes the value directly. The mathematical content is
Mathlib's: `σ` maps elements integral over `𝒪[K]` to integral elements,
and `IsIntegralClosure.equiv` identifies the integral closure with
`𝒪[L]` compatibly with the inclusion into `L`.

The development checks used only `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The module compiled with no
errors or warnings. Inspection of each theorem reported kind `theorem`,
level parameters `[u]`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The sole explicit import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Statements`.
It imports the published
[definition module](Definitions.md), which imports
`Mathlib.RingTheory.IntegralClosure.IntegralRestrict` and so provides
`algebraMap_galRestrict'_apply`. No preservation theorem (M139.001),
automorphism-group homomorphism (M139.005), action (M139.006) or later
NYLL unit is imported, stated or proved. Nothing here concerns ideals,
residue fields, inertia or reciprocity.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The full file has SHA-256
`5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`, which
matches the NYLL verification manifest in the attribution supplement.
Lines 1–100 were read, including the imports, the preservation theorem at
34–48, the restriction definition at 52–65 and both evaluation lemmas.

| Partition unit | Original declaration in `LocalFieldTheory` | Original lines | Adapted theorem in `Langlands.NYLL.LocalFieldTheory` | Proved target |
| --- | --- | --- | --- | --- |
| M139.003 | `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` | 70–78 | `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` | `GaloisGroupIntegerRingEquivOfIsIntegralClosureApplyStatement` |
| M139.004 | `galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply` | 83–91 | `galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply` | `GaloisGroupIntegerRingEquivOfIsIntegralClosureSymmApplyStatement` |

The unit identifiers come from the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m139).
The original lemmas have the same hypotheses and equalities, in the same
orientation, but with every parameter in the theorem signature. Each is
preceded by a doc comment and `@[simp]` (lines 67–69 and 80–82). Their
proofs are `rfl`, because the original restriction is built from subtype
constructors with values `σ (x : L)` and `σ.symm (x : L)`.

Worker 382 made these changes on 27 October 2026:

- added the `Langlands.NYLL` namespace prefix;
- gave each theorem its published closed target as its complete type, so the
  parameters are introduced in the proof;
- replaced both `rfl` proofs with `algebraMap_galRestrict'_apply`, as the
  published definition uses `galRestrict'` and `rfl` does not apply;
- dropped the `@[simp]` attributes. Lean accepts the attribute on these
  theorems, but in a private check neither `simp` nor
  `simp only [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]` made
  progress on the forward equation, because the type is a named proposition;
- replaced the source's NYLL imports with the published statement module.

The doc comments are rewritten to describe the adapted results.
Worker 106 suggested the `algebraMap_galRestrict'_apply` route in the task
specification. No draft from another worker was used. The published
definition, statements and Mathlib are reused by import and declaration name;
their code is not copied here.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
I checked `notes/errata/` in the project and in the current Library notes
for either registration on 27 October 2026 and found nothing. This was a
check of those two locations only. The partition records no patch10
modification to this source module.

The Lean file keeps the original copyright and author header verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither the NOTICE nor the supplement's five `ANTHROPIC_FLT_SOURCE.md`
inventories has an entry for `GaloisIntegerRing.lean`. No third-party
source listed there is copied into this unit.
