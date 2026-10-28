# Residue evaluation and base-residue fixedness: proofs

This module proves the two published closed statement targets for NYLL
source units M160.002 and M160.004. Both concern the published residue-field
equivalence
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure`.
The first theorem evaluates it on a residue class with a given integer
representative. The second shows that it fixes the image of the base residue
field. Nothing else is exported.

## Theorems and their exact targets

| Theorem in `Langlands.NYLL.LocalFieldTheory` | Its complete type |
| --- | --- |
| `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue.{u}` | `GaloisGroupResidueFieldEquivOfIsIntegralClosureResidueStatement.{u}` |
| `galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap.{u}` | `GaloisGroupResidueFieldEquivOfIsIntegralClosureAlgebraMapStatement.{u}` |

Each theorem has the one universe parameter `u`, no other declaration
parameters and no premises. Its type is the published proposition itself.
The [statement module](Statements.md) is unchanged, so every quantifier is
inside the target. For all `K L : Type u` with `Field` and `ValuativeRel`
instances, an `Algebra K L`, the
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
instance, the `IsIntegralClosure 𝒪[L] 𝒪[K] L` instance and every
`σ : Gal(L/K)`, the targets state:

- residue evaluation: for every `x : 𝒪[L]`,
  `galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (IsLocalRing.residue 𝒪[L] x) = IsLocalRing.residue 𝒪[L] (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x)`;
- base-residue fixedness: for every `x : 𝓀[K]`,
  `galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (algebraMap 𝓀[K] 𝓀[L] x) = algebraMap 𝓀[K] 𝓀[L] x`.

Here `𝒪[F]` is `Valuation.integer (ValuativeRel.valuation F)`, `𝓀[F]` is
`IsLocalRing.ResidueField 𝒪[F]`, the quotient by the maximal ideal, and
`IsLocalRing.residue 𝒪[F]` is the quotient map. `Gal(L/K)` is the group
`L ≃ₐ[K] L` of `K`-algebra automorphisms; it does not assume that `L/K` is
Galois. The scalar structures are the canonical Mathlib ones also used by the
statements. The algebra `𝒪[K] → 𝒪[L]` is
`Valuation.HasExtension.instAlgebraInteger`, the restriction of
`algebraMap K L`. The map `algebraMap 𝓀[K] 𝓀[L]` is
`IsLocalRing.ResidueField.instAlgebra` for that local homomorphism. This
module adds no hypothesis and no instance.

## Implemented proofs

The Mathlib lemmas cited below are at the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

### Residue evaluation (M160.002)

The proof introduces `K`, `L`, the seven instances, `σ` and `x`. It then
closes the goal with `IsLocalRing.ResidueField.map_residue`, applied to the
integer-ring restriction `e = galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ`
coerced to a ring homomorphism `𝒪[L] →+* 𝒪[L]`, and to `x`. That lemma, in
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`, states
`ResidueField.map f (residue R r) = residue S (f r)` for a local
homomorphism `f`, and holds by `rfl`.

`exact` accepts the lemma by definitional unfolding. The published residue
definition is `IsLocalRing.ResidueField.mapEquiv e`. The forward function
of `mapEquiv e` is `IsLocalRing.ResidueField.map (e : 𝒪[L] →+* 𝒪[L])`,
which Mathlib records as `IsLocalRing.ResidueField.mapEquiv_apply`.
Applying the coerced ring homomorphism to `x` is applying `e` to `x`. The
required `IsLocalHom` instance for the coerced equivalence is Mathlib's
`isLocalHom_toRingHom`, found by instance search. No rewriting is needed.

### Base-residue fixedness (M160.004)

The proof introduces the same data and an element `x : 𝓀[K]`, then runs
these steps:

1. `IsLocalRing.residue_surjective` gives a base integer `a : 𝒪[K]` with
   `x = IsLocalRing.residue 𝒪[K] a`, and `x` is replaced by this class.
2. Rewriting with Mathlib's `IsLocalRing.ResidueField.algebraMap_residue`
   turns both sides into residue classes of `algebraMap 𝒪[K] 𝒪[L] a`.
3. Rewriting with the first theorem,
   `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L σ`, turns the
   left side into the class of `e (algebraMap 𝒪[K] 𝒪[L] a)`.
4. `congrArg (IsLocalRing.residue 𝒪[L])` and `Subtype.ext` reduce the goal
   to an equality in `L` between the values of `e (algebraMap 𝒪[K] 𝒪[L] a)`
   and `algebraMap 𝒪[K] 𝒪[L] a`.
5. Rewriting with the published forward evaluation
   `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ` replaces the
   left side by `σ` applied to the value of `algebraMap 𝒪[K] 𝒪[L] a` in `L`.
6. `exact σ.commutes (a : K)` closes the goal. `AlgEquiv.commutes` states
   `σ (algebraMap K L (a : K)) = algebraMap K L (a : K)`. The value of
   `algebraMap 𝒪[K] 𝒪[L] a` in `L` is definitionally `algebraMap K L (a : K)`,
   as recorded by Mathlib's `Valuation.HasExtension.val_algebraMap`, which
   is proved by `rfl`.

Step 5 is the only place where the integer-ring restriction is evaluated.
The published integer-ring definition uses Mathlib's `galRestrict'` packaged
by `AlgEquiv.ofAlgHom`, so its value in `L` is not available by `rfl`. The
proof uses the published, separately accepted theorem for it. The fixedness
of base integers under the restriction is the local consequence of steps 4–6;
no fixedness or preservation premise is assumed or exported.

### Checks

The development checks used only `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The module compiled with no
errors or warnings. Inspection of each theorem reported kind `theorem`,
level parameters `[u]`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. These are author checks; they do not
replace exact-target validation or independent review.

## Imports and scope

The two explicit imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs`,
  the published [forward and inverse evaluations](../GaloisIntegerRing/Proofs.md)
  of the integer-ring restriction. Only the forward theorem
  `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` is used.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.Statements`,
  the published [statement module](Statements.md). It imports the published
  [residue-field definition](Definitions.md),
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic` and
  `Mathlib.RingTheory.Valuation.Extension`, which supply every Mathlib lemma
  used here.

Only M160.002 and M160.004 are proved. M160.003, the residue-unit formula,
is not ported. Neither are M160.005–006, the residue algebra equivalence and
its group homomorphism, or any later action, stabilizer, kernel, inertia,
ramification or reciprocity unit. No `ResidueExtension.lean` alias such as
`residueField_algebraMap_residue` or `integerRingMapOfValuationExtension`
is ported, and no global instance or simp lemma is added.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The full file has
SHA-256 `b3c47318364659eb1a14b872f8462a2284f47125b1d84391c5c93a3ba87f2c67`,
which matches the NYLL verification manifest in the attribution supplement.
Lines 1–100 were read.

| Partition unit | Original declaration in `LocalFieldTheory` | Original lines | Adapted theorem in `Langlands.NYLL.LocalFieldTheory` | Proved target |
| --- | --- | --- | --- | --- |
| M160.002 | `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue` | 43–54 | `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue` | `GaloisGroupResidueFieldEquivOfIsIntegralClosureResidueStatement` |
| M160.004 | `galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap` | 70–84 | `galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap` | `GaloisGroupResidueFieldEquivOfIsIntegralClosureAlgebraMapStatement` |

The line ranges include the doc comments; the theorem keywords are on lines
46 and 71. The unit identifiers come from the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m160).
The original theorems have the same hypotheses and equalities, in the same
orientation, but with every parameter in the theorem signature.

The original M160.002 carries `@[simp]` and is proved by `rfl`. The original
M160.004 chooses a representative with `Ideal.Quotient.mk_surjective`,
restates the goal with `change`, and rewrites with
`residueField_algebraMap_residue` from original `ResidueExtension.lean`
lines 90–96 and then with M160.002. It finishes with
`galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap` from
original `GaloisIntegerRing.lean` lines 123–134. That lemma proves that the
original restriction fixes base integers by `ext`, a `change` to the
ambient field and `σ.commutes`. The `change` relies on the original
restriction being built from subtype constructors.

Worker 761 made these changes on 28 October 2026:

- added the `Langlands.NYLL` namespace prefix;
- gave each theorem its published closed target as its complete type, so the
  parameters are introduced in the proof;
- replaced the `rfl` proof of M160.002 by the definitionally equal
  application of `IsLocalRing.ResidueField.map_residue`;
- in M160.004, used `IsLocalRing.residue_surjective` instead of
  `Ideal.Quotient.mk_surjective` and dropped the `change`. Mathlib's
  `IsLocalRing.ResidueField.algebraMap_residue` replaces the unported alias
  `residueField_algebraMap_residue`. The unported lemma
  `galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap` is
  replaced by the local steps 4–6 above. These use the published forward
  evaluation, because the published restriction uses `galRestrict'` and the
  source's `change` to the ambient field does not apply to it;
- dropped the `@[simp]` attribute of M160.002;
- replaced the source's imports with the two published modules above.

The doc comments are rewritten to describe the adapted results. Worker 106
suggested the route through `mapEquiv`, `algebraMap_residue`, the first law,
the forward evaluation and `σ.commutes` in the task specification. No draft
from another worker was used. The published definitions, statements, forward
evaluation and Mathlib are reused by import and declaration name; their code
is not copied here.

## Provenance and license

Worker 761 also read original `ResidueExtension.lean` lines 1–100, SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`, and
original `GaloisIntegerRing.lean` lines 1–135, SHA-256
`5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`.
The readable originals are in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Their attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
On 28 October 2026 I checked the project notes and the current Library notes
for errata on either registration and found none. The public partition
records no patch10 change to `ResidueGalois.lean`, and no patch10 code is
reused.

The Lean file keeps the original copyright and author header verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither the NOTICE nor the attribution supplement has an entry specific to
`ResidueGalois.lean`. No third-party source is copied into this unit.
