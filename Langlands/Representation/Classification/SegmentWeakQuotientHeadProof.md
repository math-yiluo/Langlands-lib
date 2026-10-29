# Proof of the conditional weak quotient upgrade

Authors: Worker 485 (proof design), Worker 931. The theorem
`Langlands.Classification.segmentWeakQuotientHeadUpgrade` proves the
published proposition `SegmentWeakQuotientHeadUpgrade F T` from
`Classification.SegmentWeakQuotientHeadStatement`. Strong special constituent
existence, `SegmentSpecialConstituentExistence F T`, remains an explicit
premise of that proposition; this proof neither proves nor assumes it
outside the premise.

## Proof

Fix a segment `Δ` and a representation `π` with carrier in universe
`max uF uV`.

**Weak to strong.** Suppose `T.IsSegmentQuotient Δ π`. Unfolding it gives an
actual supercuspidal representative `A` of the beginning of `Δ` (with
`hA : Δ.base.IsRepresentedBy A`), the irreducibility `hπ` of `π`, and a
surjective intertwiner `q` from the increasing product
`T.segmentInduced A.obj Δ.length Δ.rank_pos` onto `π`. The existence premise
applied to `Δ` gives some `σ` with `T.IsSegmentHead Δ σ` (its socle clause on
the decreasing product is discarded). The published `T.isSegmentHead_iff Δ σ A hA`
transports this head relation to the same representative `A`. Its
uniqueness clause gives a distinguished surjection `q₀` onto `σ` such that
every surjective intertwiner from the increasing product of `A` onto an
irreducible representation (carrier in universe `max uF uV`) has kernel
`ker q₀`.

To show `T.IsSegmentHead Δ π`, the proof keeps `A`, `hA`, `hπ`, `q` and its
surjectivity, and verifies the uniqueness clause for `q`. For a competing
surjection `q'` onto an irreducible `π'`, the clause for `σ` gives
`ker q' = ker q₀`; applied to `q` itself (with target `π.representation`,
irreducible by `hπ`) it gives `ker q = ker q₀`. The composite
`(huniq W' π' hπ' q' hq').trans (huniq _ π.representation hπ q hq).symm`
is `ker q' = ker q`.

**Strong to weak.** This direction is the published
`IsSegmentHead.isSegmentQuotient`, which forgets the uniqueness clause.

The same `π` appears throughout; no isomorphic replacement is made. Field
and carrier universes `uF` and `uV` remain independent.

## Dependency audit

The proof module imports only
`Langlands.Representation.Classification.SegmentWeakQuotientHeadStatement`.
That module imports `Classification.SegmentConstituentStatement`, whose
Langlands import closure (48 modules: `Classification.Segments`,
`Classification.ConstituentRelations`, `Classification.Supercuspidal`,
`Classification.SupercuspidalTwist`, and group, local-field, induction,
Jacquet-coinvariant, smoothness, twist and tensor infrastructure) contains
none of the declarations `SegmentSpecialEssentialSquareIntegrability`,
`SquareIntegrableLanglandsClassification`,
`SegmentEssentialSquareIntegrableClassification`,
`SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness` or
`MultisegmentSocleExhaustion`, nor any exhaustion or derivative statement.

The proof uses only the definitions `IsSegmentQuotient`, `IsSegmentHead`,
`IsIrreducibleQuotient`, `IsIrreducibleHead`, the existence premise, and the
published lemmas `isSegmentHead_iff` and `IsSegmentHead.isSegmentQuotient`.
It uses no theorem proving constituent existence, no classification, no
Jacquet calculation, no analytic or square-integrability statement, no
derivative formula (in particular not Ze80 §9.3's analytic result or the
§9.17 conjecture), and no finite-length or admissibility result. It is
therefore independent of the tasks listed in its proof task's independence
section and of their conclusions.

## Limitations

This proof is not a proof of constituent existence or of the Jacquet
exponent norm formula. It only shows that, once strong existence is
available, the weak and strong relations agree for the same `π`.
