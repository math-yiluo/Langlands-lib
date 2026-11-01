# Actual torsion cardinality from numerical polarized geometry

This internal module specializes the general
`Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankStatement`
to actual multiplication on an actual bundled abelian scheme over an
algebraically closed field. The general numerical statement remains an
explicit premise. This module does not prove that statement or the
unconditional geometric torsion rank target.

Let `B / Spec K` have specified smooth relative dimension `g`. Let `n` be
positive and nonzero in `K`. The theorem
`multiplicationFinrank_of_polarizedFiniteFlatRank` assumes an actual ample
line bundle `L` and an actual module-sheaf isomorphism

```text
[n]* L ≅ L^(tensor (n*n)).
```

Published field multiplication theorems give finiteness and etaleness of
the actual multiplication morphism, hence its flatness. Smooth relative
dimension, properness and geometric connectedness are the properties of
the same actual abelian scheme. Applying the supplied numerical statement
with `q = n*n` therefore gives native rank `(n*n)^g`. The elementary
power identities identify this with `n^(2*g)`. No degree, rank, basis or
substitute torsion object is supplied as data.

`natCard_level_of_polarizedFiniteFlatRank` composes this native-rank
calculation with `natCard_level_eq_multiplicationFinrank` from the separate
`GeometricTorsionNativeRank` comparison module. The latter counts the
existing actual `GroupScheme.Tate.Level` using the actual finite etale
kernel and native `Scheme.Hom.finrank`. It is applied at the unit image
of a point of the field spectrum. Thus the resulting cardinality formula
concerns precisely the existing actual torsion group.

`fieldTorsionCardinality_of_numericalGeometry` supplies the ample line
bundle and its pullback identity from two additional explicit premises:
`GroupScheme.FieldSymmetricAmpleExistenceStatement` and
`GroupScheme.FieldSymmetricMultiplicationPullbackStatement`. It first
obtains a symmetric ample line bundle on the actual `B`, then applies the
symmetric multiplication formula at the same `n`. Together with the
general numerical rank premise this proves the displayed universally
quantified field-level cardinality implication. The conclusion has exactly
the field-level shape needed by the separate torsion-structure and
relative-specialization reduction; it does not import or assume that
reduction.

The definition `torsionEquivFinOfNumericalGeometry` uses this proved
conditional cardinality and its positivity to select an enumeration of
the actual torsion type by `Fin (n^(2*g))`. This is an equivalence of types;
no group or residue-linear compatibility is claimed. The separate torsion
structure argument remains necessary to obtain module coordinates.

The derivation is internal: it composes the three named proposition
interfaces with the proved actual native-rank comparison and elementary
natural-number exponent identities. The interfaces' paired Markdown
explains their original-source provenance and outstanding geometry. No
new original-source result is asserted here. All three geometric premises
remain visible in the final theorem; none is claimed proved by this
module. Level one and dimension zero are included.
