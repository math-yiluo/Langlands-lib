# Finite-Galois stabilizer criterion: exact proof

This module proves
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.adjoin_le_adjoin_of_forall_fixed_imp_fixed`
with type
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.adjoin_le_adjoin_of_forall_fixed_imp_fixedStatement (K := K) (M := M)`.
It imports the existing [statement module](Statements.md) unchanged.

The theorem retains independent universes `u` and `v`, `{K : Type u}`,
`{M : Type v}`, `[Field K]`, `[Field M]`, `[Algebra K M]`,
`[FiniteDimensional K M]`, and `[IsGalois K M]`. Its proposition quantifies
over `a b : M` and assumes that every `K`-algebra automorphism of `M` fixing
`b` fixes `a`. Its conclusion is the inclusion `K⟮a⟯ ≤ K⟮b⟯`.
No additional hypothesis or instance is supplied.

## Implemented proof

After introducing `a`, `b`, and the pointwise fixing hypothesis, the proof uses
`IsGalois.fixedField_fixingSubgroup` to express `K⟮b⟯` as the fixed field
of its fixing subgroup. `IntermediateField.adjoin_le_iff` reduces the desired
inclusion to membership of the generator `a` in that fixed field; the
singleton membership equality substitutes `a` for the arbitrary generator.

By `IntermediateField.mem_fixedField_iff`, it remains to show that each
automorphism in the fixing subgroup of `K⟮b⟯` fixes `a`. Such an automorphism
fixes `b`, since `IntermediateField.mem_adjoin_simple_self K b` places `b`
in `K⟮b⟯`. The given implication then says it fixes `a`, completing the proof.
The argument uses the supplied finite-dimensional Galois hypotheses exactly
at the fixed-field correspondence.

## Provenance and modifications

The proof is adapted from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/GaloisStabilizer.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/GaloisStabilizer.lean>),
SHA-256 `e03c8bdaf43ac682a960ec61815b150bfd116f3b7975777dbf873a282f31471d`.
The theorem is at lines 34–49; its proof is at lines 40–49 and the independent
universe and field parameters are at lines 24–30. This is source unit M396.001.
The source is registered as
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 577 prefixed the original namespace with `Langlands.NYLL`, imported
the published statement instead of repeating its Mathlib imports, wrote the
full field and instance telescope directly on the theorem, and gave the
theorem the fully applied published target as its type. Introducing the
target's quantified elements precedes the unchanged original proof argument.
The source's unused `noncomputable section` is omitted. The original
copyright, author, and Apache-2.0 header are retained verbatim; the existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) supply the repository notices.
This module adds only the exact proof and changes no source interface.
