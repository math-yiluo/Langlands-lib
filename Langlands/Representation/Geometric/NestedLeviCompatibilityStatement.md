# Parameters and actual inclusions through nested Levi refinements

Author: Worker 429.

`Langlands.NestedLeviCompatibilityStatement.{uA,uK}` is a proposition
definition stating two compatibility laws. This file provides no proof.

Fix an arbitrary natural rank `n`, ordered coarse block shape `B`, refinement
`Q` of `B`, refinement `R` of `D = B.flatten Q`, and direct refinement `S`
of `B`. Retain the literal equality of ordered shapes
`h : D.flatten R = B.flatten S`. Write `C = D.flatten R`. Each flattening uses
the existing consecutive block numbering, sizes and standard coordinate
embeddings. The equality `h` transports fine-indexed functions and actual
fine product-Levi elements. No equivalence or compatibility certificate is
an input.

The first conjunct quantifies over every type `A : Type uA` and every coarse
function `a : Fin B.length → A`. Let

```text
aD(j) = a(((B.flattenBlockEquiv Q).symm j).1),
aC(k) = aD(((D.flattenBlockEquiv R).symm k).1).
```

It states equality of functions on the directly flattened fine indices:

```text
(h ▸ aC)(k) = a(((B.flattenBlockEquiv S).symm k).1).
```

Thus repeating a value through the middle parents and then the fine parents
agrees with repeating it directly from its coarse parent. Taking `A = ℝ`
recovers the parent-index convention of
`Langlands.RealTwistFamilies.restrictParameter`; taking `A = ℂ` gives the
same rule for complex determinant parameters. There is no algebraic
structure on `A`, no size weighting and no sum constraint on these values.

The second conjunct quantifies independently over every commutative ring
`K : Type uK`. For every `m : C.Levi K`, it states equality in `B.Levi K`:

```text
(flattenedLeviEquiv K B S (h ▸ m)).val
  =
(flattenedLeviEquiv K B Q
  (flattenedLeviEquiv K D R m).val).val.
```

On the left, the actual fine product is transported along `h`, identified
with `refinedLevi K B S`, and included into the coarse product. On the right,
it is first identified with `refinedLevi K D R`, included into `D.Levi K`,
and then identified with `refinedLevi K B Q` and included into `B.Levi K`.
Both routes use the existing constructed `flattenedLeviEquiv`. This law
asserts equality of the actual included matrices for every fine element.
The first parameter law alone does not establish this second law.

The two universes `uA` and `uK` are independent. All ranks allowed by
`BlockShape`, including zero, are retained; consecutive refinements may be
equal. There are no field, representation, smoothness, support, chamber,
analytic or tensor-factorization assumptions.

This is an internal derived compatibility statement. Its sole import,
`Langlands.Representation.Geometric.FlattenedLevi`, supplies the existing
ordered flattening, actual refined subgroup equivalences and ambient
embedding identities. The intended proof obligations are finite-coordinate
parent identification using the standard coordinate embeddings, followed by
the equality of ambient Levi embeddings and injectivity of the coarse
embedding. No external literature theorem is invoked.

The statement constructs no induced family and asserts no induction or
Jacquet comparison, occurrence, branch persistence, analytic continuation,
cone bound, multiplicity equality, irreducible head or all-regular
comparison theorem. Those remain separate obligations.
