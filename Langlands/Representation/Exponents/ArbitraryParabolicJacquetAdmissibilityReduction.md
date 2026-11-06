# Actual Jacquet admissibility reduced to dynamic structure

Author: Worker 1218.

This internal assembly uses the published dynamic contraction, rational open-cell,
Levi realization and actual normalized-Jacquet admissibility results. It keeps
`ParabolicDynamicStatement` and `DynamicGeometricUnipotentRadicalStatement`
as explicit structural hypotheses. It does not prove the unconditional
`ArbitraryParabolicJacquetAdmissibilityStatement`.

`ArbitraryParabolicJacquetAdmissibilityReductionStatement` is the Prop-valued
definition of the implication from those two structural propositions to the
unchanged global admissibility proposition. The companion theorem
`arbitraryParabolicJacquetAdmissibility_of_dynamic` proves this conditional
implication.

The generic bridge
`Jacquet.HasOppositeIwahoriContractionBasis.hasIwahoriContractionBasis`
uses the induced topology on the Levi subgroup. An open subgroup of the Levi is
the preimage of an ambient open identity neighborhood. An ambient-cofinal
opposite contraction basis supplies a compact open subgroup inside that
neighborhood, whose Levi intersection is contained in the prescribed subgroup.

`RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis` works for any
cocharacter of the connected reductive group over a nonarchimedean local field,
in the canonical rational-point topology. The ambient local compactness and
nonarchimedean-group instances are explicit. The result uses the published
uniform contraction by one Levi-central cocharacter point, closedness of both
dynamic radicals, unique opposite-radical/centralizer/radical factorization,
and the rational open-cell identity-neighborhood theorem. The comparison of
the affine point topology with the scheme-chart topology supplies the topology
used by the open-cell theorem.

`pointImage_radical_eq_dynamic` identifies the literal point image of the
supplied geometric radical with the dynamic radical, assuming the displayed
parabolic has the same all-test-scheme range as the dynamic parabolic and
assuming the dynamic geometric-radical statement. The forward inclusion uses
the published radical membership equivalence. For the reverse inclusion, a
dynamic radical point lies in the parabolic range, and the same membership
equivalence lifts it to the supplied radical.

`arbitraryParabolicJacquetAdmissibility_of_dynamic` first uses the two structural
hypotheses to realize the supplied parabolic and rational Levi by a single
cocharacter. It identifies the literal radical and Levi point images, obtains
the dynamic contraction basis above, and applies the published admissibility
theorem for the actual normalized Jacquet functor. This retains the actual
coinvariant quotient and inverse-half Haar-modulus twist. The field and
representation-carrier universes remain independent, and the representation
requires only source admissibility. The supplied radical and multiplication
isomorphism are the data of the original proposition.

No standard-cocharacter realization, simultaneous standard basis, finite
length or finite generation is used by this reduction. The two structural
inputs remain separate proof obligations. This module is derived by
composition of published declarations; it asserts no additional external
structural theorem.
