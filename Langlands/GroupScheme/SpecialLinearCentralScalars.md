# Scalar roots of unity in the full centre of a special-linear group

This internal construction embeds scalar roots of unity into the actual
special-linear group scheme over any commutative affine base. A root of unity
of order dividing `n` defines its scalar `n` by `n` matrix, whose determinant
is one. The resulting matrix map is multiplicative and commutes with every
coefficient map.

The actual roots-of-unity kernel and special-linear point equivalences
transport this map to every relative test scheme. Naturality gives the actual
group-scheme morphism `scalarRootsOfUnityHom n R`. All its image points belong
to the full scheme-theoretic centre: after any further restriction, their
matrices are scalar and hence commute with every special-linear matrix.
For positive degree, evaluation at one diagonal entry makes this map injective
on the points of every test scheme.

The contragredient automorphism acts by inversion on this scalar subgroup.
Its matrix formula transposes the inverse scalar matrix, which is the scalar
matrix of the inverse root. The natural point equivalences give the stated
identity on every test scheme. These results retain nonreduced tests and
impose no characteristic restriction.

For `n > 2` and a nontrivial base ring `R`, the implemented proof detects a
moved central point on the actual quotient spectrum
`Spec (R[X]/(X^n - 1))`. Its universal root cannot satisfy `X^2 - 1`: the latter
polynomial is nonzero and has smaller natural degree than the monic defining
polynomial. Mathlib's `AdjoinRoot.mk_ne_zero_of_natDegree_lt` therefore says its
class in the quotient is nonzero. Inversion cannot fix the universal root of
unity, since an inversion-fixed unit has square one.

The affine point equivalence for the actual roots-of-unity kernel turns this
coordinate into a point of `mu`. Its scalar image is central by the all-test
centrality theorem above. If the contragredient fixed the full centre, its
inversion formula and injectivity of the scalar map would force the universal
root to equal its inverse, contradicting the polynomial calculation. This
proves `not_automorphismFixesCenter_contragredientIso` and exhibits an actual
`HasCenterMovingAutomorphism` for the split special-linear group. The quotient
test is used as it stands, including when it is nonreduced; neither reduced
tests nor field-valued points replace it.

This is an internal construction and deduction from the published actual
special-linear, roots-of-unity, contragredient and full-centre interfaces,
together with Mathlib's polynomial quotient facts. It is not a transcription
of a literature theorem. It does not construct an automorphism of an exceptional
anisotropic kernel from Cartan data, classify automorphisms of division norm-one
groups, or prove the local rank-one enumeration.
