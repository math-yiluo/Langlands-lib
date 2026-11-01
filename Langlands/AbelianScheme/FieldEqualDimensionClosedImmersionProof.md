# A closed abelian subscheme of full dimension

`Langlands.AbelianScheme.fieldEqualDimensionClosedImmersion` proves exactly
`FieldEqualDimensionClosedImmersionStatement.{u}`. The field and universe are
arbitrary, and the dimension `g` may be zero. The proof uses the existing actual
abelian schemes, their actual homomorphism, and its underlying scheme map.

The target is geometrically integral by the published
`smoothGeometricIntegrality` theorem. Over a field spectrum this makes it
integral, so its underlying space is irreducible and its structure sheaf is
reduced. Geometric connectedness makes the source nonempty and connected.
Properness of the two structure maps makes both underlying spaces compact.

A closed point of the source exists by compactness. At that point the published
`fieldSmoothClosedPointStalkDimension` identifies stalk dimension with `g`.
The private lemma bounds the dimension of every stalk by the dimension of
the whole space: the stalk dimension is the coheight of the point, and
Mathlib's order isomorphism with irreducible closed subsets bounds this
coheight by their Krull dimension. Thus the source has dimension at least `g`.
The closed embedding, with codomain restricted to its range, is inducing,
so its image has dimension at least that of the source.

The published `fieldSmoothTopologicalKrullDim` bounds the target dimension
by `g`. If the closed image were proper, the published
`Picard.topologicalKrullDim_add_one_le_of_isClosed` would bound its dimension
plus one by the target dimension. In `WithBot ℕ∞` this implies that the
image dimension is strictly less than the natural number `g`, contradicting
the lower bound. The range is therefore the whole target. Mathlib's
`isIso_of_isClosedImmersion_of_surjective`, applied to the reduced target,
finishes the proof.

This is an internal derivation from the named published geometric results
and Mathlib's coheight and closed-immersion facts. It proves no relative
dimension equality for the actual torsion closure, numerical torsion formula,
or density assertion. Its conclusion is an isomorphism of underlying schemes;
no inverse in the abelian-scheme category is separately constructed here.
