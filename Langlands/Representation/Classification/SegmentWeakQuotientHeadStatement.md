# Conditional weak quotient to strong head upgrade

Authors: Worker 485 (design), Worker 931. This module defines one
proposition, `Langlands.Classification.SegmentWeakQuotientHeadUpgrade F T`.
It asserts no proof and assumes no theorem as data.

## Statement

Fix a prime `p`, an actual finite extension `F : PadicField p` of `ℚ_p` and
a compatible topological realization `T : F.TopologicalData`. The
proposition says: if the published `SegmentSpecialConstituentExistence F T`
holds, then for every segment `Δ : T.Segment` and every smooth complex
representation `π` of `GL_{mr}(F)` (with `m = Δ.length`, `r = Δ.rank`,
`mr = Δ.degree`) whose carrier lies in universe `max uF uV`,

`T.IsSegmentQuotient Δ π ↔ T.IsSegmentHead Δ π`.

The topology on the field is exactly `T.topology`. The representation `π`
is the same on both sides of the equivalence; no isomorphic replacement is
made.

The relations come from `Classification.Segments` and
`Classification.ConstituentRelations`:

- `T.IsSegmentQuotient Δ π` (the weak relation): for some actual
  supercuspidal representative `A` of the beginning `ρ` of `Δ`, `π` is
  irreducible and there is a surjective intertwiner from the increasing
  product `ρ × νρ × ⋯ × ν^(m-1) ρ` onto `π`.
- `T.IsSegmentHead Δ π` (the strong relation): for some such `A`, `π` is
  irreducible, there is a surjective intertwiner `q` from the increasing
  product onto `π`, and every surjective intertwiner from that product onto
  an irreducible representation with carrier in the same universe has the
  same kernel as `q`. That is, `π` is the unique irreducible quotient
  object, not only the unique isomorphism class.
- `SegmentSpecialConstituentExistence F T` (Ze80 §9.1 via Proposition 2.10,
  stated in `Classification.SegmentConstituentStatement`): for every segment
  some `π` satisfies `T.IsSegmentHead Δ π`, together with a socle condition
  on the decreasing product.

Strong existence is kept as an explicit premise. The proposition neither
asserts nor proves it, and the weak hypothesis on `π` is not strengthened.

## Universes

The field universe `uF` and the supercuspidal carrier universe `uV` are
independent. The target carrier universe is `max uF uV`, the universe of the
induced representations. Taking `uV := max uF uV` gives the saturated case
used by `SegmentSpecialJacquetExponentNormFormula`, whose segments are
`T.Segment.{max uF uV, uF}`.

There are no assumptions of unitarity, admissibility, finite length or
square integrability.

## Provenance

This is an internal consequence of the published constituent relations and
their representative transport (`isSegmentHead_iff`) in
`Classification.Segments`. It does not restate an original source theorem.
The reason it holds: a strong head has one kernel shared by all irreducible
quotient maps out of the increasing product. Once such a head exists, the
kernel of any supplied irreducible quotient map equals that shared kernel,
so the supplied map can serve as the distinguished map in the uniqueness
clause. The reverse implication forgets the uniqueness clause. This
paragraph is provenance, not a Lean proof.

The interface lets a consumer that assumes only the weak relation, such as
`SegmentSpecialJacquetExponentNormFormula`, use strong-head properties once
strong existence is available.

## Limitations

The premise is essential to this interface. This statement does not assert
or prove special constituent existence, special constituent uniqueness, or
the Jacquet exponent norm formula. Compiling the definition establishes
nothing.
