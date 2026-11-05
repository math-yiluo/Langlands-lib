# Compact open subgroups of the actual finite adelic point group

For an affine group scheme over a number field and a specified algebraic
matrix representation, `RepresentationGrowth.finiteMatrix` is the
actual representation map on finite adelic points followed by the
existing general-linear point homeomorphism. Its preimage of the actual
standard integral matrix subgroup is an open subgroup.

If the algebraic representation is a closed immersion, the actual
finite adelic map is a closed embedding: finite adeles are Hausdorff,
and the previously proved affine-point closed-immersion theorem applies.
The standard integral matrix subgroup is compact, including rank zero.
Its preimage under that closed embedding is therefore compact.

For every affine group scheme locally of finite type over the number
field, the published closed linear embedding theorem supplies such a
representation. This proves existence of an actual compact open subgroup
without a new algebraic premise. `FiniteAdelicGroupPoints.compactOpenSubgroup`
chooses one and exports its compactness. The choice is not used to define
the group, its topology or its rational points.

This is an internal construction from the existing actual affine-point
map, the algebraic closed linear embedding proof and the existing
standard integral subgroup compactness proof. It uses neither reduction
theory nor finite volume. No smoothness, reductivity, splitness or
positive-rank condition is needed.
