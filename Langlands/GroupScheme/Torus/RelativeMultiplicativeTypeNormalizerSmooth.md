# Smooth normalizers of subgroups of multiplicative type

This internal development proves that every supplied representative of the
normalizer of a closed multiplicative-type subgroup of a smooth relatively
affine group is smooth over the original arbitrary base scheme. The subgroup
need not be smooth: its finitely generated abelian character groups may have
torsion. `relativeMultiplicativeTypeSmoothNormalizerModel` chooses an actual
closed representative and records both its smoothness and its full all-test
normalizer property.

First, a finitely generated abelian group's algebra is finitely presented
over any commutative coefficient ring. Over the integers it is finite type
and the integers are noetherian, so it is finitely presented; tensor extension
identifies its base change with the required group algebra.

The finite tensor-equation lemmas imply that a finitely generated subgroup
ideal with projective quotient coordinates has a finitely generated normalizer
ideal. The two pieces are the coefficient ideals of the universal conjugate
and inverse conjugate applied to that subgroup ideal. The module also records
that the centralizer ideal is finitely generated when the ambient coordinate
algebra is finite type, by testing equality of its two universal-product maps
on finitely many algebra generators.

For a closed diagonalizable subgroup over an affine base, identify the quotient
of the ambient coordinate algebra with the subgroup's group algebra. It is
projective and finitely presented over the base. Since the ambient smooth
coordinate algebra is also finitely presented, its quotient kernel is finitely
generated. Hence so is the full normalizer ideal, and the normalizer coordinate
quotient is finitely presented without a noetherian hypothesis.

The published normalizer square-zero lifting theorem applies to arbitrary
abelian character groups and to the smooth ambient coordinate algebra. It
makes that quotient formally smooth. Finite presentation therefore gives
smoothness of its spectrum. Uniqueness of represented subgroup schemes
transports this to any supplied normalizer representative.

Finally, affine open covers extend this argument from coefficient rings to
arbitrary base schemes for diagonalizable subgroups. Smoothness descends along
the fppf cover on which a multiplicative-type subgroup becomes diagonalizable.
The chosen model combines this result with the published closed normalizer
representability theorem. No quotient existence assertion is included in this
unit.
