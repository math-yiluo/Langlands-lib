# Actual compact equal-rank coefficient tests

Author: Worker 408.

This internal module defines `HasEqualRankCompactTest`: actual vectors in the
two specified coefficient images, a Schwartz--Bruhat function, a compact
mirabolic set containing the identity, and a compact open ambient subgroup
satisfying the six published `IsEqualRankCompactTest` conditions.

The construction theorem `hasEqualRankCompactTest_of_kirillov` assumes
`WhittakerTypeKirillovStatement` separately in the two independent carrier
universes. It uses the published compact mirabolic tests and the conditional
coefficient-model topology-transfer theorem to lift them. For the second
representation it reinterprets the inverse standard character as the standard
character of `ψ.scale (-1)`, retaining the same linear functional and the same
underlying mirabolic test function. A preimage vector in that coefficient image
then gives a vector for the original inverse-character functional with
identical function values.

Smoothness supplies a common compact open right stabilizer in determinant
absolute value one. The published row-orbit theorem supplies its exact
Schwartz indicator and mirabolic factorization. The mirabolic product
indicator lemma, the two coefficient lifts, and these stabilizer and row
identities establish the six assembly conditions.

The method `HasEqualRankCompactTest.one_mem_equalRankRationalValues` works
over any topological field with the stated measurable structures, Borel
structure on the quotient, and a compatible quotient measure whose unipotent
measure is right invariant. The thickened quotient set is compact and open.
It contains the quotient image of the identity since the mirabolic set
contains the identity. Compatibility therefore makes its mass positive and
finite. The published compact-assembly normalization theorem then gives
literal rational value one for every natural parameter `q`. This step uses
no numerical formula for the quotient volume and no general analytic
continuation theorem.

This is an internal deduction from the imported Library definitions and
theorems. It uses actual coefficient images and retains every supplied
topology, rank one, independent carrier universes, and possibly reducible
Whittaker-type representations. It proves no Kirillov surjectivity and does
not prove the unconditional `EqualRankUnitValueStatement`.

The completed pair compiled with zero errors and warnings in the approved
environment. Inspection of `HasEqualRankCompactTest` reports a Prop-valued
definition with independent `uF`, `uV`, `uW` and only `propext`,
`Classical.choice`, and `Quot.sound`. Development compilation is not
independent acceptance or proof of the unconditional parent target.
