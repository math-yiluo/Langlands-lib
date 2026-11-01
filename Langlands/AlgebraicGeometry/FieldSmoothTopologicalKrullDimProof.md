# The dimension of a quasi-compact smooth scheme over a field (proof)

Authors: Worker 921 wrote the proof; Worker 1162 rechecked it against the current Library and
submitted it.

This module proves `Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement`
(module `Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement`):

```lean
theorem Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim :
    FieldSmoothTopologicalKrullDimStatement.{u}
```

So if `X` is quasi-compact and `f : X ⟶ Spec k` is smooth of relative dimension `g` over a
field `k`, then `topologicalKrullDim X ≤ g`. The proof uses no `sorry` and no new axioms. It
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

- `FieldSmoothTopologicalKrullDim.topologicalKrullDim_le_of_stalk (X : Scheme.{u})
  [CompactSpace X] (g : ℕ)
  (h : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) ≤ g) :
  topologicalKrullDim X ≤ g`. On a quasi-compact scheme, a bound on the dimension of the
  stalks at closed points bounds the dimension of the space.
- `fieldSmoothTopologicalKrullDim : FieldSmoothTopologicalKrullDimStatement.{u}`, the target.

## Proof

`topologicalKrullDim X` is by definition the Krull dimension of the poset
`IrreducibleCloseds X`. By Mathlib's `Order.krullDim_eq_iSup_coheight`, this is the supremum
of the coheights of its elements. Let `T` be an irreducible closed set.

- `T` is closed and nonempty in the quasi-compact `T0` space `X`, so it contains a point `c`
  with `{c}` closed (Mathlib's `IsClosed.exists_closed_singleton`).
- The irreducible closed set `C = {c}` lies in `T`, so `coheight T ≤ coheight C`
  (`Order.coheight_anti`).
- Mathlib's order isomorphism `irreducibleSetEquivPoints` between irreducible closed sets and
  points with the specialization order sends `c` to `closure {c} = {c}`. So
  `coheight C = coheight c` (`Order.coheight_orderIso`).
- By Mathlib's `ringKrullDim_stalk_eq_coheight` (Stacks Tag 02IZ),
  `coheight c = ringKrullDim (X.presheaf.stalk c)`, which is at most `g` by hypothesis.

This proves `topologicalKrullDim_le_of_stalk`. For the target, the Library's published theorem
`Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension`
(module `Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof`) gives
`ringKrullDim (X.presheaf.stalk x) = g` at every closed point `x` of a scheme smooth of
relative dimension `g` over a field. `topologicalKrullDim_le_of_stalk` then applies, using the
`CompactSpace X` hypothesis of the statement.

## Provenance

The statement Markdown records the derived provenance and its source records. Every nonempty
closed subset of a quasi-compact scheme contains a closed point, and a chain of irreducible
closed subsets whose smallest member contains a closed point `c` gives a chain of primes in the
stalk at `c` (compare Stacks Tag 0A21, item (5), for locally algebraic `k`-schemes, as cited in
the statement Markdown). The Lean proof expresses this through coheight in the poset of
irreducible closed subsets, as described above, rather than through explicit chains of primes.
