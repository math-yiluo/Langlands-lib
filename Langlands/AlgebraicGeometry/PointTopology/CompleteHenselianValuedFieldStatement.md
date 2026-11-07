# Complete valued fields are henselian

Author: Worker 105.

Statement `Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldStatement`.

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.14 (registered source `conrad-2011-weil-grothendieck-adelic-points`). Conrad defines a valued
field as a field with a nontrivial absolute value, henselian if this absolute value extends
uniquely to every algebraic extension. He adds: "The complete case is all we will actually need,
so the reader may skip ahead to Proposition 5.4 and restrict attention to complete ground
fields." The results he then applies to complete fields (Lemma 5.3, Proposition 5.4,
Proposition 5.11, Corollary 5.12) are stated for henselian valued fields. So the remark
presupposes that complete valued fields are henselian. This statement records that fact.

## Formalization

```lean
def CompleteHenselianValuedFieldStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K], IsHenselianValuedField K
```

- A valued field is a nontrivially normed field: the norm is the nontrivial absolute value.
- `IsHenselianValuedField K` is the Library's definition of Conrad's henselian valued fields:
  for every algebraic extension field `L : Type u` of `K`, there is exactly one absolute value
  on `L` extending the norm of `K`.
- Completeness is `CompleteSpace K` for the metric of the norm.

Both archimedean and non-archimedean fields are included. The universe `u` is arbitrary, and the
extension fields range over `Type u`, as in `IsHenselianValuedField`.
