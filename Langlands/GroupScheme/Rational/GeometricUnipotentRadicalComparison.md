# Comparing geometric unipotent radical predicates

Author: Worker 1355.

This internal comparison relates `IsGeometricUnipotentRadical` from
`Rational.SemistandardIntersection` to
`LeviSubgroup.IsGeometricUnipotentRadical` from `Rational.LeviSubgroup`.
The latter consists of both a ground-field radical and an algebraic-closure
radical. The former gives the same subgroup properties over the ground
field and maximality only over the algebraic closure.

The forward comparison from the Levi predicate to the semistandard predicate
is unconditional. For the reverse comparison the ambient group is affine
and the existing proposition `UnipotentFieldExtensionStatement.{u}` is an
explicit hypothesis. No proof of that structural proposition is claimed.
Every field and universe is allowed. The construction
`LeviSubgroup.geometricUnipotentRadicalEquiv` is the canonical equivalence
of the two witness types supplied by the proved biconditional
`leviSubgroup_isGeometricUnipotentRadical_iff`. Its forward map extracts the
fields; its inverse performs the descent argument below. Its inverse laws
hold by proof irrelevance.

To descend greatestness, take any smooth connected unipotent normal closed
subgroup over the ground field. Closedness in the affine ambient group
makes it affine, and smoothness gives finite type. The existing geometric
connectedness theorem keeps it connected after extension to the algebraic
closure. The explicit unipotence-preservation hypothesis makes the base
change unipotent, while closedness, smoothness and normality are preserved
by existing base-change results. Geometric greatestness therefore gives
containment after base change. The existing fpqc reflection theorem
`SubgroupFunctor.le_range_of_baseChange_le` descends that containment on
all test schemes. Smoothness and closedness of the base-changed radical,
together with the remaining geometric fields, give the second radical
required by the Levi predicate.

The result concerns actual morphisms and arbitrary test schemes, including
nonaffine and nonreduced tests. It supplies no radical representative,
dynamic unipotence, unipotence-preservation proof, rational Levi existence,
or proof of `ParabolicRadicalTorusLeviStatement`. Its provenance is the
published predicate definitions and the already proved fpqc and geometric
connectedness interfaces; no new external structural assertion is used.
