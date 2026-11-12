# Strong Langlands heads of all multisegments

Author: Worker 4880.

The theorem `Langlands.Classification.multisegmentHeadExistence` proves the
unchanged published proposition
`Langlands.Classification.MultisegmentHeadExistence.{uF,uV} F T` from
[MultisegmentClassificationStatement](MultisegmentClassificationStatement.md).
It adds no hypothesis. Its only outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`,
and the universes `uF` and `uV` stay independent. For every multisegment
`a : T.Multisegment.{max uF uV, uF}`, including the empty one, it supplies a
smooth representation `π` of `GL_(a.degree)(F)`, with carrier universe
`max uF uV`, such that `a.IsLanglandsHead π`.

`Multisegment.IsLanglandsHead`, in
[LanglandsData](LanglandsData.md), asks for a segment-product datum `d` at the
same rank with `d.multisegment = a` and `d.IsLanglandsHead π`. The latter
contains the nonprecedence ordering of `d`, the segment-head property of its
blocks, and the strong head certificate `IsIrreducibleHead` for the induced
product. That certificate is the strong one: it gives a surjective
intertwiner onto the irreducible `π` and equality of the kernels of all
irreducible quotient maps.

## Implemented proof

The proof is a composition of two published Library theorems.

1. Given `a`, the second clause of
   `multisegmentConstituentDataExistence.{uF,uV} F T a`, from
   [MultisegmentConstituentDataExistenceProof](MultisegmentConstituentDataExistenceProof.md),
   supplies a datum `d : T.SegmentProductDatum.{max uF uV, uF} a.degree` with
   `d.multisegment = a`, `d.IsPrecedenceOrdered` and `d.HasSegmentHeads`.
   That proof enumerates `a` in a nonprecedence order, with total degree
   `a.degree`, and chooses an actual special segment head for each block.
2. `orderedMultisegmentHeadExistence.{uF,uV} F T`, from
   [OrderedMultisegmentHeadExistenceProof](OrderedMultisegmentHeadExistenceProof.md),
   applied at rank `a.degree` to `d` and those two hypotheses, supplies `π`
   with `d.IsLanglandsHead π`. That proposition is Rodier's Theorem 3(a)
   for one ordered product of segment heads; its proof covers rank zero.
3. The anonymous constructor `⟨π, d, hd, hπ⟩` then gives the existential of
   `MultisegmentHeadExistence` and the witness for `a.IsLanglandsHead π`.

The empty multisegment needs no separate case. It has degree zero, the first
step applies to it as to any multisegment, and the second step at rank zero
is covered by the rank-zero case of its published proof.

## Provenance

The target is Rodier (1982), §4.3 Theorem 3(a), printed p.211 (PDF p.12),
with Zelevinsky (1980) §§6.5 and 9.1 for the enumeration of a multisegment
and for segment heads. The registered sources and their locators are in the
target's companion Markdown. This module only composes the two proved
Library theorems above; it uses no statement or pending task as an input,
and it leaves the target pair and all imported pairs unchanged. Lean reports
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
