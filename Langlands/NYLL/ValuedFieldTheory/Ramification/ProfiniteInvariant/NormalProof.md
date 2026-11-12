# Normality of maximal residue extensions of profinite invariant rings

The theorem `Langlands.NYLL.RamificationTheory.Ideal.Quotient.normal_of_profinite`
proves exactly the published closed proposition
`Langlands.NYLL.RamificationTheory.Ideal.Quotient.normal_of_profiniteStatement.{u, v, w}`.
The sole import is
`Langlands.NYLL.ValuedFieldTheory.Ramification.ProfiniteInvariant.NormalStatement`.
Neither the statement pair nor its imports is changed.

The three universes of the rings `A`, `B` and the group `G` remain independent.
The proof introduces the statement's complete telescope, including the implicit
`G` and all its instances although `G` does not occur in the conclusion.
It retains maximal ideals `P : Ideal A` and `Q : Ideal B` with `Q.LiesOver P`.
The conclusion concerns the actual fields `A ⧸ P` and `B ⧸ Q`, with the local
`Ideal.Quotient.field` instances and Mathlib's `Ideal.Quotient.algebraOfLiesOver`.
There is no additional Hausdorffness, finite-group or injective-algebra-map
hypothesis. The hypotheses are exactly those documented in the imported
[statement companion](NormalStatement.md).

## Implemented proof

This is the finite-orbit proof from Naganori Yamaguchi's NYLL M242.001.
The subsingleton case for `B` contradicts maximality of `Q`. In the other case,
`Algebra.IsInvariant.isIntegral_of_profinite` makes `B` integral over `A`;
Mathlib's quotient integrality supplies the algebraicity part of `Normal`.

For the splitting part, represent an element of `B ⧸ Q` by `x : B`.
Continuity into the discrete ring makes its stabilizer open. The compact,
totally disconnected topological-group API supplies an open normal subgroup
`N` inside that stabilizer. The element `x` then lies in the subalgebra `B'`
fixed by `N`, with the finite quotient `G ⧸ N` acting on `B'` and invariant
ring `A`.

The orbit characteristic polynomial of `x` in `B'` is monic and lifts to a
polynomial `p : A[X]`, by `Algebra.IsInvariant.charpoly_mem_lifts` and
`Polynomial.lifts_and_degree_eq_and_monic`. Mapping `p` to `(A ⧸ P)[X]`
produces a polynomial vanishing at the original residue class of `x`. The
proof explicitly checks the coefficient maps through `B'`, `B` and the
quotients. Thus the minimal polynomial divides this residue polynomial.
After mapping into `(B ⧸ Q)[X]`, the orbit polynomial is a product of linear
factors. Its monicity makes it nonzero, and `Polynomial.Splits.of_dvd`
therefore gives splitting of the minimal polynomial.

The proof uses Mathlib directly through the two imports of the statement,
`Mathlib.FieldTheory.Galois.Profinite` and
`Mathlib.RingTheory.Invariant.Profinite`. In particular it uses the fixed-point
subalgebra and finite-quotient invariant-action instances, the open-normal
subgroup theorem, the invariant orbit characteristic polynomial, quotient
algebra maps, minimal-polynomial divisibility and polynomial splitting.
It does not invoke the finite-group theorem `Ideal.Quotient.normal` or any
other NYLL proof module. It supplies this residue-normality theorem only;
no class-formation, cup-product, Tate, transfer or reciprocity assertion is
proved here.

## Source correspondence and attribution

The original is Naganori Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/ProfiniteInvariant.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/ProfiniteInvariant.lean#L26-L101).
The source telescope is at lines 28–38, the theorem at lines 45–47 and its
proof at lines 48–99. The full file was read; its SHA-256 is
`16a8b3a7e109a3a3ac55f3ef4133488713c3d049d9f095b79415d71153ae213e`.
The registered snapshot is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source is locally readable below
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Worker 94 adapted the proof on 11 November 2026. The namespace gains
`Langlands.NYLL`, and the theorem's type is the published closed proposition
rather than a section telescope. A single `intro` supplies the complete
original telescope, including the role of the source's `include G`.
The proof body from source lines 48–99 is unchanged. The source's
`noncomputable section`, `open scoped Pointwise` and local quotient-field
instance are retained. The imported statement already contains the original
two Mathlib imports. These are packaging changes; the proof route is the
source route. The source module docstring's word “prime” is corrected to
“maximal” here to agree with both the source theorem and the published target.

The original copyright, Apache-2.0 notice and authorship header are preserved
verbatim. The existing [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) are retained without change;
the source author is Naganori Yamaguchi (assisted by OpenAI Codex).
The Library target and its documentation were extracted by Worker 179.

## Validation

The project Lean service compiled this module without errors or warnings in
the supplied Lean 4.34.0 environment, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. A Lake build with declaration
inspection also succeeded: the declaration is a theorem with exactly the
universe parameters `u`, `v`, `w`, using only `propext`, `Classical.choice`
and `Quot.sound`. The theorem's declared type is the exact published
`normal_of_profiniteStatement.{u, v, w}`. Independent semantic review,
exact-target validation and publication remain separate from compilation.
