# Degree and Frobenius fixed points in a residue algebraic closure (targets)

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M236.009 | `finrank_finiteResidueGaloisIntermediateFieldIn` (97–110, `@[simp]`) | `finrank_finiteResidueGaloisIntermediateFieldInStatement` (`abbrev`) |
| M236.011 | `mem_range_algebraMap_iff_frobenius_fixed_in` (145–170) | `mem_range_algebraMap_iff_frobenius_fixed_inStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Let `k : Type u` be a field with `[Fintype k]` and `Omega : Type v` a
`k`-algebra field.

- M236.009 (source `omit [Algebra.IsAlgebraic k Omega]`): for
  `[IsAlgClosed Omega]`, `n : ℕ` and `[NeZero n]`, the finite Galois
  intermediate field `finiteResidueGaloisIntermediateFieldIn k Omega n` has
  `Module.finrank k` equal to `n`. Parameters, in order: `k`, `[Field k]`,
  `[Fintype k]`, `Omega`, `[Field Omega]`, `[Algebra k Omega]`,
  `[IsAlgClosed Omega]`, `n`, `[NeZero n]`.
- M236.011 (source `omit [IsAlgClosed Omega]`): for
  `[Algebra.IsAlgebraic k Omega]` and `x : Omega`, `x` lies in the range of
  `algebraMap k Omega` if and only if the arithmetic Frobenius
  `FiniteField.frobeniusAlgEquivOfAlgebraic k Omega` fixes `x`. Parameters, in
  order: `k`, `[Field k]`, `[Fintype k]`, `Omega`, `[Field Omega]`,
  `[Algebra k Omega]`, `[Algebra.IsAlgebraic k Omega]`, `x`.

These are the parameter lists of the source theorems (checked with `#check`);
each statement uses every one of its section binders.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; each source theorem is replaced by a
  Prop-valued definition with the `Statement` suffix whose body is the source
  proposition verbatim, under the source's `variable` blocks (lines 39–41) and
  its `omit … in` commands. Source proofs are omitted; nothing is proved here.
- The target of the source `@[simp]` theorem M236.009 is an `abbrev`, so that a
  later proof `theorem … : …Statement …` can carry the attribute.
- Neither proposition mentions `FiniteField.Extension`, so the private instance
  M236.001 is not needed in these statements; the private instances
  M236.002–M236.004 are not used by them either. No instance is declared.
- Imports: the sibling `Initial/Definitions` module. The `open` commands are
  those of the `Definitions` module.

A private probe (not part of this unit) proves both targets with the source
proofs (for M236.009, with the M236.001 value supplied by a local `have`).

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
