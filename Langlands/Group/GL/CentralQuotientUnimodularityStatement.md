# Right invariance of Haar measures on actual p-adic GL central quotients

Author: Worker 576.

`Langlands.GLCentralQuotientHaarRightInvariantStatement.{uF}` is a closed
Prop-valued definition. It states that every Haar measure on the full central
quotient of a positive-rank p-adic general linear group is right invariant.
This pair defines the proposition; it contains no proof of the proposition.

## Exact binders and conclusion

The statement quantifies over every natural prime `p`, its `Fact p.Prime`
instance, every `F : PadicField.{uF} p`, and every supplied
`T : F.TopologicalData`. It installs exactly `T.topology` on `F.Carrier`.
The matrix unit group `GeneralLinear n F.Carrier` then has its induced
topology, and its actual quotient

```text
Q = GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)
```

has the quotient topology. The center is the full group center.
The rank binder is `n : ℕ` followed by the hypothesis `0 < n`.

For that rank, the statement installs `T.centralQuotientMeasurableSpace n`,
the Borel sigma algebra of this same quotient topology. It then quantifies
over every `μ : MeasureTheory.Measure Q` and every instance
`[μ.IsHaarMeasure]`. No normalization is chosen. Its conclusion is exactly
`MeasureTheory.Measure.IsMulRightInvariant μ`: for each `q : Q`, pushforward
of `μ` by `x ↦ x * q` equals `μ`.

There is no representation or representation-carrier universe in this
proposition. It requires no additional regularity or unimodularity premise,
and it applies to each supplied compatible topology rather than choosing
`F.canonicalTopologicalData`. The only new Lean declaration is this proposition
definition. Its direct import is
`Langlands.Representation.Classification.Tempered`, which provides the existing
`centralQuotientMeasurableSpace` abbreviation.

## Internal provenance and separate proof obligation

This is an internal, derived interface for the right-translation step in the
integral-form proof of square-integrable unitarity. The motivation is
W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995, §2.5, printed/PDF pp.28–29,
especially Proposition 2.5.4. The registered source is
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
These two pages were read directly. Casselman's coefficient identity uses
right translation, and the integral construction requires the corresponding
measure invariance. This GL-specific proposition isolates that obligation;
it is not a claim that arbitrary locally compact groups are unimodular.

The existing
`GLBlockCentralQuotientTopologyStatement` and
`glBlockCentralQuotientTopology` supply Hausdorffness, local compactness,
second countability, Haar existence and sigma-finiteness for the actual
central quotient. Likewise `T.exists_isHaarMeasure_centralQuotient n`
ensures that the measure quantification here is not vacuous.
Those existence and topology results alone do not prove right invariance.

The current Library also supplies
`PadicField.TopologicalData.centralQuotientHaar_rightInvariant` in
`Langlands.Group.GL.CentralQuotientMeasure`. That theorem covers every rank
and every Borel measurable realization for the supplied topology. A separate
proof of this exact closed statement can specialize that theorem to
`T.centralQuotientMeasurableSpace n`, using `T.centralQuotientBorelSpace n`,
and then restrict to positive rank.
The existing theorem derives right invariance from the triviality of positive
characters on the full central quotient, applied to its modular character,
and regular Haar uniqueness. Its algebraic argument is Worker 116's
diagonal/transvection proof, exposed and used in Worker 386's quotient
construction. Those implementations remain unchanged; this pair neither
reimplements their proofs nor asserts that Haar existence proves their result.

The separate exact proof must establish the displayed conclusion for every
measure binder with the specified instances. Constructing an invariant
positive form or proving square-integrable unitarity remains the obligation
of the consuming representation-theoretic task.
