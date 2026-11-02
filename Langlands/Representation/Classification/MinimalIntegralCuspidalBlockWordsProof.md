# Proof that global minimality forces each decreasing block word

Authors: Worker 320 (shared Lean proof and initial explanation), Worker 438
(exact-target verification, dependency audit and expanded explanation).

The theorem `Langlands.Classification.minimalIntegralCuspidalBlockWords`
proves exactly the proposition
`Langlands.Classification.MinimalIntegralCuspidalBlockWords.{uF,uV} F T`.
Its outer parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)`
and `(T : F.TopologicalData)`. Field and carrier universes remain independent;
all actual representation carriers are in `Type (max uF uV)`. The proof
introduces precisely the hypotheses of the unchanged published target.

For each coarse irreducible factor, `integralCuspidalConstituentWord` chooses
an actual integral cuspidal Jacquet word which permutes the labels of its
input inner cuspidal product. The positive rank needed there follows from
the coarse block shape. `integralCuspidalJacquetWord_concatenate` reassembles
these actual occurrences through normalized Jacquet refinement, using the
supplied actual coarse tensor occurrence in the ambient Jacquet module.

The pointwise permutations give `List.Forall₂ List.Perm` between
`List.ofFn w` and the reference block list
`List.ofFn (fun i => List.ofFn (e i))`, using their equal lengths and indexed
entries. `List.Perm.flatten_congr` gives a permutation of the full reference
word. The supplied minimality is applied only to this concatenated word,
with both its actual realization and its permutation witness. Thus the
restricted minimality hypothesis suffices; no assertion about arbitrary
unrelated words is used.

`Combinatorics.eq_blocks_of_minimal_flatten` shows that every block is
unchanged: a decreasing block is lexicographically greatest among its
permutations, and a first unequal block would make the concatenation smaller.
The fixed lengths of the paired blocks ensure that suffixes cannot reverse
that comparison. Injectivity of `List.ofFn` returns the pointwise block
equalities and transports the actual occurrences to the reference words.

The provenance is internal composition of the published constituent-word,
normalized Jacquet refinement, actual tensor-subquotient and finite-list
results, followed by elementary order reasoning. The support and embedding
provenance of the lower constituent-word theorem is documented in its
published paired explanation. The two new helper pairs explain the
implemented dependent rank transports and the first-unequal-block argument.

The reference concatenation need not be assumed to occur in advance.
There is no positive-total-rank assumption: `B.positive i` supplies exactly
the positive rank needed for each selected coarse constituent. For a shape
with no coarse slots the conclusion is vacuous. The ambient `π` need not
be irreducible, admissible, finite length or square integrable. Repeated
integer labels and their multiplicities are retained throughout. The
conclusion supplies actual Jacquet tensor subquotients for each original
decreasing block.

At Library base `a5dff2ff93bd3637a67ee8847f67f811efc82f01`, the conservative
project import closure has 634 modules, including these three new modules.
All 1,262 existing dependency Lean/Markdown files, including the target
pair and its entire import closure, are unchanged. The additional
classification-named branches contain supplied segment data, elementary
support/list constructions, relative statement interfaces and lower
support, tensor, finite-length, induction and Jacquet results. In particular,
the import of `SegmentProductConcatenation` supplies the finite-list identity,
with supplied actual segment data in its other declarations; it does not
import segment classification.

The closure and the invoked proof routes use no segment classification,
multisegment exhaustion, ordered strong-head existence, quotient coverage,
tempered block uniqueness, square-integrable Langlands classification,
square-integrable exhaustion, regular exhaustion or proof successor of
these results. This prerequisite leaves identification of a special segment
constituent, initial integral-line existence and the parent analytic
classification as separate obligations.
