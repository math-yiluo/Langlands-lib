# NYLL M395.001: multiset product valuation comparison

The paired module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity.MultisetProductComparison`
proves `Langlands.NYLL.PortInternal.M395.d001Statement` by the theorem
`Langlands.NYLL.PortInternal.M395.d001.{u, v}`. Its type is the complete closed
Library target, with no additional parameters or assumptions:

```lean
∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {α : Type v} (s : Multiset α) (f g : α → R)
  (h : ∀ z ∈ s,
    IsDiscreteValuationRing.addVal R (f z) ≤
      IsDiscreteValuationRing.addVal R (g z)),
  IsDiscreteValuationRing.addVal R ((s.map f).prod) ≤
    IsDiscreteValuationRing.addVal R ((s.map g).prod)
```

The ring and multiset elements have independent universes. The hypothesis is
restricted to membership in `s`. Empty multisets, repetitions, and zero factors
are allowed; the valuation takes values in `ℕ∞`, including `⊤`.

## Implemented proof

After introducing the target's entire telescope, the proof uses
`Multiset.induction_on`. For the empty multiset the two products coincide, so
`le_rfl` closes the inequality. In the cons case, `Multiset.map_cons` and
`Multiset.prod_cons` separate the head factor from the tail product.
`IsDiscreteValuationRing.addVal_mul` rewrites each product valuation as a sum
in `ℕ∞`. The theorem `add_le_add` combines the head inequality, obtained from
`h` using `Multiset.mem_cons_self`, with the induction hypothesis. To use that
hypothesis, the proof restricts `h` to the tail, whose members also belong to
the cons multiset. No cancellation, finiteness of valuations, decidable equality,
or nonzero-factor hypothesis is used.

The only import is the published `PolynomialRootProximity.Statements` module.
It supplies the unchanged target and the Mathlib multiset, valuation, and order
interfaces used by the proof. This module supplies only M395.001.

## Source and modifications

The proof is adapted from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PolynomialRootProximity.lean`.
The original private theorem `Polynomial.Splits.addVal_multiset_prod_le`
has its signature at lines 34–42 and its proof at lines 43–54. The complete
[pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PolynomialRootProximity.lean>)
was read; its SHA-256 is
`fd5707f0f811be973bcba0f0cc9ad3779344dd958da1af8b8647307cc953775d`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 573 retained the source induction proof, replaced the direct Mathlib
imports with the Library statement import, and changed the private source name
to the published internal name. The theorem is stated as the closed
`d001Statement.{u, v}`, and its complete telescope is introduced inside the proof.
The independent universe `v` of the source's `{α : Type*}` is retained explicitly.
The source's polynomial scope and noncomputable section are unnecessary here
and omitted. Neither the target nor its imported Lean/Markdown pairs is edited.

The original copyright and author header is preserved verbatim, followed by a
modification notice. The Library's existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged.

## Development check

The module compiled with no errors or warnings through `lean_check` in approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Declaration inspection identified
`d001` as a theorem with universe parameters `u, v`, depending only on the
standard assumptions `propext`, `Classical.choice`, and `Quot.sound`.
The theorem's declared type is the unchanged closed target itself. Development
compilation and inspection do not supply independent acceptance or publication.
