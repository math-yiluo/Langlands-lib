# Targets for the finite indices of the residue datum

This module states, as Prop-valued targets, the two public theorems M238.003
and M238.004 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709` (121 lines, SHA-256
`0ffd3ceea309047d8e54275d4680c8c86ea3dd071ad786a71df35f18642bfbdf`).
M238.003 is at lines 65–107 (signature lines 67–71) and M238.004 at lines
109–118 (signature lines 112–115). Both use the section variables of lines
31–33. Neither theorem is proved here: each proof will be a separate
`lean.proof@1` contribution, under the source theorem's adapted name, once
these targets are in the Library.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The definition M238.001 `residueDatumIn` that both targets use is in the
sibling [`Definitions.lean`](Definitions.lean). The work is part of Task 5862.

## The targets

Both targets are in namespace `Langlands.NYLL.LocalClassFieldTheory`, with
`Langlands.NYLL.RamificationTheory` and `Langlands.NYLL.ClassFormation` open.
They have the same parameters, all explicit or instance-implicit as in the
source:

- `k Omega : Type`, both in universe level 0 as in the source;
- the six instances of the source's section variables, in their order:
  `[Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]`, so that `Omega` is an
  algebraic closure of the finite field `k`;
- `E : FiniteGaloisIntermediateField k Omega`, a finite Galois intermediate
  field of `Omega / k` (Mathlib's `FiniteGaloisIntermediateField`).

The source declares `k`, `Omega` and the six instances as section variables.
Lean includes an unused section instance in a Prop-valued definition only if
the definition mentions it. To be certain that none is dropped, each target
writes all of them as explicit binders, in the source's order.

### M238.003

```lean
def residueDatumIn_fieldImage_closedFixingSubgroupStatement
    (k Omega : Type)
    [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  (residueDatumIn k Omega).fieldImage
      (closedFixingSubgroup k Omega E) =
    (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup
```

This is the source statement
`(residueDatumIn k Omega).fieldImage (closedFixingSubgroup k Omega E) =
(zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup`.
Here `closedFixingSubgroup k Omega E` (Library NYLL M087.001,
`Langlands/NYLL/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup/Definitions.lean`)
is the Krull-closed subgroup `Gal(Omega/E)` of automorphisms fixing `E`. The
coercion takes `E` to its underlying intermediate field. `DegreeData.fieldImage`
(Library NYLL M010) is the image of that subgroup under the degree
homomorphism, a subgroup of `ZHatMul = Multiplicative ZHat`. On the right,
`zHatMulNat n : ContinuousAddMonoidHom ZHat ZHat` (Library NYLL M009.002,
`Langlands/NYLL/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U002/Definitions.lean`)
is multiplication by the natural number `n`, `x ↦ n • x`. Its underlying
additive homomorphism (`toAddMonoidHom`) has range the additive subgroup
`n ZHat`, viewed by `AddSubgroup.toSubgroup` as a subgroup of
`Multiplicative ZHat`. So the target says: if `n = [E : k]`, the residue degrees
of the automorphisms fixing `E` are exactly the multiples of `n` in `ZHat`.

### M238.004

```lean
def Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement
    (k Omega : Type)
    [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  ((residueDatumIn k Omega).fieldImage
      (closedFixingSubgroup k Omega E)).index = Module.finrank k E
```

This is the source statement
`((residueDatumIn k Omega).fieldImage (closedFixingSubgroup k Omega E)).index
= Module.finrank k E`. `Subgroup.index` is Mathlib's index, a natural number
that is `0` for infinite index. The target says that the degree image of
`Gal(Omega/E)` has index `[E : k]` in `ZHatMul`. The source places the theorem
in the sub-namespace `Internal`; its documentation string calls it an internal
finite-coordinate calculation, because the public residue-degree interfaces use
`Cardinal` or a bundled finite residue field. The target keeps the
sub-namespace.

## The `IsGalois` instance

`closedFixingSubgroup k Omega E` needs an instance `IsGalois k Omega`. In the
source, it comes from the private instance `residueAlgebraicClosureIsGalois`
(M236.003, `ResidueAlgebraicClosureDegree.lean` lines 50–52, proved by
`infer_instance` from the private instance `residueAlgebraicClosureIsAlgClosure`
(M236.002, lines 47–48, `⟨inferInstance, inferInstance⟩`)). The source imports
it through M237. The Library adaptation of M236 publishes no such instance, and
the task contract forbids turning the private instances into global ones. So
each target supplies the two facts locally, by `haveI` in its body:

- `IsAlgClosure k Omega` from `IsAlgClosed Omega` and
  `Algebra.IsAlgebraic k Omega`, by the anonymous constructor exactly as in
  M236.002;
- `IsGalois k Omega` by `{}`. Its two fields, `Algebra.IsSeparable k Omega`
  and `Normal k Omega`, are found by instance search. Separability holds
  because `k` is finite, hence perfect (Mathlib's `Mathlib.FieldTheory.Perfect`,
  imported for this), and `Omega / k` is algebraic. Normality holds because
  `Omega` is an algebraic closure. In the approved Mathlib, `infer_instance`
  alone does not find `IsGalois k Omega`, because Mathlib's
  `IsAlgClosure.isGalois` instance requires `CharZero k`.

Both facts are propositions, so any proof of them is definitionally equal to
any other. A later proof that obtains `IsGalois k Omega` in another way meets
these targets without conversion. A focused check (lean_check
`47ef640b-eae2-47eb-b138-e4d12d477806`) confirmed this on the M238.003 shape:
it compiled the `haveI` form and proved it equivalent, by `Iff.rfl`, to the
same proposition stated with section-local instances. No instance, global or
local, is declared by this module.

## The private lemma M238.002

The source's private lemma `mem_fixingSubgroup_iff_restrictNormalHom_eq_one`
(M238.002, lines 41–63) states that `sigma` fixes `E` exactly when its
restriction `AlgEquiv.restrictNormalHom E sigma` is the identity. It is used
only in the proof of M238.003. Following the task contract, it is not stated
here; it will be proved inside the M238.003 proof and recorded in that proof's
Markdown. A focused check (lean_check
`b1c21d0f-d04b-47b4-81fd-868c171f8faf`) confirmed that the source proof of
M238.002 compiles unchanged in the approved environment.

## Exact declaration map and modifications

| Source declaration | Adapted target |
| --- | --- |
| `LocalClassFieldTheory.residueDatumIn_fieldImage_closedFixingSubgroup` (M238.003) | `Langlands.NYLL.LocalClassFieldTheory.residueDatumIn_fieldImage_closedFixingSubgroupStatement` |
| `LocalClassFieldTheory.Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup` (M238.004) | `Langlands.NYLL.LocalClassFieldTheory.Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement` |

The changes are these:

- Each source theorem becomes a Prop-valued `def` named with the suffix
  `Statement`, whose body is the theorem's statement. The documentation
  strings say "Target" but otherwise keep the source wording.
- The section variables become explicit binders of each target, in the
  source's order and binder kinds.
- `IsAlgClosure k Omega` and `IsGalois k Omega` are supplied by `haveI` in
  each body instead of the source's imported private instances (see above).
- The namespaces gain the prefix `Langlands.NYLL`.
- The NYLL imports become the Library modules that publish the reused
  declarations: this module's `Definitions` (M238.001, which brings in the
  Library adaptations of M010 and M236), the Library adaptation of M087
  (`closedFixingSubgroup`), and the Library adaptation of M009.002, the natural
  multiplication (`zHatMulNat`). The Mathlib modules
  `Mathlib.FieldTheory.Perfect` (for the separability instance) and
  `Mathlib.GroupTheory.Index` (for `Subgroup.index`) are imported explicitly.
- The module documentation keeps the substance of the original summary and
  adds the adaptation record.

Nothing else changes in the statements. In environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), against Library
`2016a0d994180c702214a75514a08546aa930f07`, `lean_check`
`62717269-ba0e-4b83-a58e-0377213a340a` (M238.003 target) and
`d0965583-6a6f-4699-988f-3dd83e6a482a` (M238.004 target) compiled the module
with 0 errors and 0 warnings. For each target they report kind `definition`,
`statement_returns_prop: true`, level parameters `[]`, and the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are kept
unchanged. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 59 checked the original source and the reused Library and Mathlib
declarations, wrote these targets and this documentation in November 2026.
The Lean header records the modifications.
