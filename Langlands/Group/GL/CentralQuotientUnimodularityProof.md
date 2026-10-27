# Right invariance of Haar measures on actual p-adic GL central quotients: proof

Author: Worker 378.

`Langlands.glCentralQuotientHaarRightInvariant` proves the exact closed
proposition `Langlands.GLCentralQuotientHaarRightInvariantStatement.{uF}`
from `Langlands.Group.GL.CentralQuotientUnimodularityStatement`. Its type is
that proposition, with the same universe parameter `uF`.

## Implemented proof

The proof is a short specialization of an existing Library theorem. It
introduces the prime `p`, its `Fact p.Prime` instance, the field
`F : PadicField.{uF} p` and the supplied `T : F.TopologicalData`. Then it
installs `T.topology` on `F.Carrier`, exactly as the statement does. Next it
introduces the rank `n` and the hypothesis `0 < n`. It installs
`T.centralQuotientMeasurableSpace n` on the actual quotient
`GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`.
Finally it introduces an arbitrary measure `μ` on this quotient and its
`IsHaarMeasure` instance.

The proof also records `T.centralQuotientBorelSpace n`, published in
`Langlands.Representation.Classification.Tempered`. That theorem states that
the installed measurable structure is a `BorelSpace` for the quotient
topology determined by `T.topology`. The proof then applies
`PadicField.TopologicalData.centralQuotientHaar_rightInvariant T n` from
`Langlands.Group.GL.CentralQuotientMeasure` to `μ`. That theorem quantifies
over every measurable structure on the quotient with a `BorelSpace` instance,
and over every Haar measure on it. Its instance arguments are filled by the
installed measurable structure, its `BorelSpace` proof and the `IsHaarMeasure`
instance of `μ`. Its conclusion is exactly
`MeasureTheory.Measure.IsMulRightInvariant μ`.

The positivity hypothesis `0 < n` is not used: the reused theorem holds for
every rank, including zero. The proof chooses no topology, measurable
structure or Haar normalization, and adds no regularity or unimodularity
premise. Every binder of the statement remains universally quantified.

## Reused results

All mathematical content comes from the published theorem
`PadicField.TopologicalData.centralQuotientHaar_rightInvariant`. As documented
in `Langlands/Group/GL/CentralQuotientMeasure.md`, that theorem obtains
Hausdorffness, local compactness and second countability of the quotient from
`glBlockCentralQuotientTopology`. With these, Mathlib infers that each Haar
measure on the quotient is regular. The theorem then applies
`GeneralLinear.haar_centralQuotient_isMulRightInvariant`, which proves right
invariance of every regular Haar measure on the full central quotient. By
`GeneralLinear.centralQuotient_positiveCharacter_eq_one`, built on Worker 116's
diagonal/transvection argument, the modular character of the quotient is
trivial. Regular Haar uniqueness then identifies each right translate of the
measure with the measure itself. Those declarations are imported unchanged;
this file adds only the wrapper theorem.

The proof imports `Langlands.Group.GL.CentralQuotientUnimodularityStatement`
and `Langlands.Group.GL.CentralQuotientMeasure`. Its axioms are the standard
`propext`, `Classical.choice` and `Quot.sound`.
