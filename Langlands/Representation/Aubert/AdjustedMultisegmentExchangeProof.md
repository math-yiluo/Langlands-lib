# Actual adjusted Aubert exchange for a multisegment: proof

Module `Langlands.Representation.Aubert.AdjustedMultisegmentExchangeProof`.

The theorem `Langlands.Aubert.adjustedMultisegmentExchange` has type
`Langlands.Aubert.AdjustedMultisegmentExchangeStatement.{uF, uV} F T`, the
exact Library proposition from
[AdjustedMultisegmentExchangeStatement](AdjustedMultisegmentExchangeStatement.md).
It holds for every prime `p`, every `F : PadicField.{uF} p` and every
`T : F.TopologicalData`, with independent field and representation universes
`uF` and `uV`.

## What is proved

Fix a rank `n`, data `dZ dL : T.SegmentProductDatum.{max uF uV, uF} n`, actual
smooth complex representations `Z` and `L` of `GL_n(F)`, witnesses
`hZ : dZ.IsZelevinskySubrepresentation Z` and `hL : dL.IsLanglandsQuotient L`,
and an equality `dZ.multisegment = dL.multisegment`. Then

```text
adjustedOperator F T n [Z] = [L]
```

Here `adjustedOperator` is the actual support-adjusted Aubert operator of
`Aubert/SupportSign`, and each bracket is the exact class
`GeneralLinear.finiteLengthClass n F.Carrier`. The finite-length proofs are
`SmoothRep.hasFiniteLength_of_isIrreducible` applied to the irreducibility
witnesses in `hZ` and `hL`. The case `n = 0` is included. The theorem has no
hypothesis beyond the data of the statement.

## Notation

Write `t` for the graded operator `gradedAdjustedOperator F T`. For a label `c`
in rank `m`, write `[c]` for `basisClass F T m c`. "`c` is a label of `a`" means
`IsLabel F T a m c`: some irreducible representative of `c` is a weak Zelevinsky
subrepresentation for a datum with multisegment `a`.

## The proof

The proof uses five published theorems:

- `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`
- `binaryProductExactness`
- `gradedInductionRingLaws`
- `HeadProductLeadingTerm.exists_socleLabel_of_isLanglandsQuotient`
- `LanglandsHeadDuality.isLabel_unique`

The proof goes as follows.

1. The first three theorems give a unitary additive character `ψ` and the
   structural witnesses `hx := binaryProductExactness F T` and
   `hl := gradedInductionRingLaws F T hx`. Label uniqueness needs these
   witnesses.
2. `HeadProductLeadingTerm.exists_socleLabel_of_isLanglandsQuotient`, applied to
   `dL`, `L` and `hL`, gives a label `c` of `dL.multisegment` in rank `n` with
   `t [c] = [class of L]`. That theorem obtains a strong Langlands head of the
   multisegment, applies `LanglandsHeadDuality.gradedAdjustedOperator_label`, and
   identifies that head with `L` by the ordered head classification
   `Classification.orderedMultisegmentHeadClassification`.
3. The class of `Z` is also a label of `dL.multisegment`. The witness is `Z`
   itself with the datum `dZ`, the relation `hZ` and the equality
   `dZ.multisegment = dL.multisegment`.
4. `LanglandsHeadDuality.isLabel_unique F T hx hl ψ` says that two labels of the
   same multisegment in the same rank are equal. So `c` is the class of `Z`.
5. Rewriting with `basisClass_irreducibleIsoClass` turns both basis classes into
   `gradedInclusion F T n` of exact finite-length classes. Then
   `gradedAdjustedOperator_homogeneous` moves `t` inside as the rank-`n`
   operator `adjustedOperator F T n`.
6. Evaluating both graded classes at rank `n`, `gradedInclusion_apply_self`
   gives the rankwise equality of the statement.

## Scope and what is not used

The proof uses only published Library theorems. It adds no duality,
classification, polynomial-comparison or multiplicativity hypothesis. It
replaces no part of the actual operator by an opaque one.

The theorem is an equality of exact Grothendieck classes. It constructs no
duality functor and no representation isomorphism. It says nothing about the
correctness of the separate Moeglin–Waldspurger algorithm.

## Provenance

The statement is a derived internal bridge, not a numbered literature theorem.
The route is also derived and internal. It rests on a rank-order induction, which
is already carried out in the published
`LanglandsHeadDuality.gradedAdjustedOperator_label`, for strong heads.
The published `HeadProductLeadingTerm` extends it to weak Langlands quotients.
This proof only combines those results with label uniqueness.

Checked with Lean: 0 errors and 0 warnings. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`, and the level parameters are `uF` and `uV`.
