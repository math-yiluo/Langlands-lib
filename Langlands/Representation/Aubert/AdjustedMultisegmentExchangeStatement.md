# Actual adjusted Aubert exchange for a multisegment

`Langlands.Aubert.AdjustedMultisegmentExchangeStatement.{uF, uV} F T`
is a derived, internal proposition target joining the existing multisegment
label relations to the existing actual support-adjusted Aubert operator.
It is stated for every prime `p`, `PadicField.{uF} p` named `F`, and
`F.TopologicalData` named `T`. The field and representation universes are
independent; all representation carriers have universe `max uF uV`.

For every natural rank `n`, the statement takes separate data
`dZ dL : T.SegmentProductDatum.{max uF uV, uF} n`, actual smooth complex
representations `Z` and `L` of `GL_n(F)`, witnesses
`hZ : dZ.IsZelevinskySubrepresentation Z` and
`hL : dL.IsLanglandsQuotient L`, and an equality
`dZ.multisegment = dL.multisegment`. Its conclusion is the unsigned equality

```text
adjustedOperator F T n [Z] = [L].
```

Here each bracket is exactly `GeneralLinear.finiteLengthClass n F.Carrier`
in the existing Grothendieck group of actual finite-length smooth
representations modulo actual short exact sequences. The finite-length
proofs are supplied by `SmoothRep.hasFiniteLength_of_isIrreducible` applied
to the irreducibility witnesses already contained in `hZ` and `hL`.
There is no separate finite-length premise.

The weak relations retain their existing meanings: both data are
precedence-ordered; the blocks of `dZ` are segment socles and `Z` is an
irreducible subrepresentation of their induced product; the blocks of `dL`
are segment heads and `L` is an irreducible quotient of their induced
product. The orderings and block representatives may differ, subject to
the displayed equality of their actual multisegments. The statement also
applies to strong multisegment socles and heads by choosing their witnessing
data and using the existing weakening lemmas
`SegmentProductDatum.IsZelevinskySocle.isZelevinskySubrepresentation` and
`SegmentProductDatum.IsLanglandsHead.isLanglandsQuotient`.

The provenance is the internal bridge between the label definitions in
`Classification/LanglandsData` and `Aubert/SupportSign`'s actual
`adjustedOperator`. The existing segment exchange, adjusted multiplicativity,
socle-product rank triangularity and ordered head classification motivate a
proof of this bridge; this module supplies its reusable proposition only.
It makes no claim that this precise weak-relation formulation is a separately
numbered theorem in the original literature.

The scope includes rank zero and uses the current p-adic GL models and their
normalization conventions. The operator is the existing support-sign
adjustment of the actual alternating induction–Jacquet operator, extended
along the proved Jordan–Holder comparison. No duality, classification,
polynomial comparison, or multiplicativity hypothesis is added to the
proposition. The equality concerns exact classes; this module asserts no
construction of a duality functor or representation isomorphism, and no
correctness of the separate Moeglin–Waldspurger algorithm. Proving the
proposition remains a separate obligation.
