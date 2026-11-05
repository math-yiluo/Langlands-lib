# The identity parabolic and its canonical trivial radical

Author: Worker 1597.

This internal derived construction supplies actual identity-parabolic data
for the normalized-tempered central-character proof. It uses the published
definitions of parabolic and rational Levi subgroups, the represented unit
subgroup, triviality of the unipotent radical of a connected reductive group,
base change of unipotence and smooth connected affine groups, and actual Borel
existence. It introduces no additional source assertion.

For a connected reductive group over any field, the identity inclusion is
closed and the group is smooth. An actual Borel subgroup of the base change
to the algebraic closure factors through the identity, proving the
parabolic condition. The canonical unit subgroup is the ground-field
unipotent radical by the published trivial-radical theorem. Its closedness,
smoothness, connectedness, unipotence and normality survive the indicated
base change. Every competing geometric normal unipotent subgroup has
trivial image by connected reductivity, so geometric greatestness holds.

Multiplication of the identity Levi with this unit subgroup equals the
right unitor of the cartesian monoidal category of schemes over the field.
It is therefore an isomorphism. These facts verify the full rational Levi
predicate. `IdentityParabolicData` packages the parabolic and Levi conditions
for the identity inclusion, the canonical geometric radical and the matching
multiplication isomorphism; `identityParabolicData` constructs the package.

The field and group universe is arbitrary. This module makes no claim
about center quotients, character unitarity, or comparison of a Jacquet
quotient with the original representation.
