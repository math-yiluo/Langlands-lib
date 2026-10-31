# Proof: the origin local-dimension bound from a finite rational translation stabilizer

This module proves the Library proposition
`Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u}`
(from `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement`),
for an arbitrary universe `u`:

```lean
theorem Langlands.AbelianScheme.algClosedFieldRigidifiedPicardOriginDimensionLowerBound :
    AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u}
```

The statement says the following. Let `k` be an algebraically closed field and `A` an
abelian scheme over `Spec k` of relative dimension `g`. Let `P` be a locally finite type
scheme over `Spec k` and `U` an actual rigidified family on `P` that is universal for all
tests. Suppose some actual line bundle `L` on `A` is isomorphic to its pullback along only
finitely many rational translations. Then the stalk of `P` at the published origin point
`fullPicardOriginPoint k A U hU` has Krull dimension at least `g`. The statement and its
import closure are used unchanged; the proof adds no hypotheses.

## Implemented proof

The proof is a single application of the conditional theorem
`Langlands.AbelianScheme.algClosedFieldRigidifiedPicardOriginDimensionLowerBound_of_stalkDimension`
from the helper module `Langlands.AlgebraicGeometry.Picard.PicardOriginMumfordClassifier`
(submitted with this proof; see its Markdown for the full construction). That theorem
takes two generic statements as hypotheses, and this module supplies both from their
published proofs:

- `Langlands.AlgebraicGeometry.quasiFiniteAtStalkDimension :
  QuasiFiniteAtStalkDimensionStatement.{u}`, from
  `Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof`: for a locally finite type
  morphism `f : X ⟶ Y` that is quasi-finite at `x`,
  `ringKrullDim O_{X,x} ≤ ringKrullDim O_{Y,f x}`;
- `Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension :
  FieldSmoothClosedPointStalkDimensionStatement.{u}`, from
  `Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof`: at a closed point
  of a scheme smooth of relative dimension `g` over a field, the stalk has Krull dimension
  `g`.

In outline, the helper argues as follows. The Mumford family of `L` (rigidified along the
unit section using triviality of line bundles over a field) is classified by a morphism
`classifier : A.X ⟶ P` sending the unit to the origin. Its fibre over the origin consists of
rational translations stabilizing `L` up to isomorphism, so it is finite by hypothesis, and
`classifier` is quasi-finite at the unit. The unit is a closed point of the smooth scheme
`A`, so its stalk has dimension `g` by the second statement. The first statement then gives
`g = dim O_{A,e} ≤ dim O_{P,origin}`.

## Scope

This module and the helper prove only the conditional dimension bound. They do not prove
or assert the existence of an ample line bundle or of a line bundle with finite
stabilizer; such a bundle is a hypothesis of the statement. Inspection of the theorem
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`. No literature
result is used beyond the published Library and Mathlib declarations named here and in
the helper's Markdown.
