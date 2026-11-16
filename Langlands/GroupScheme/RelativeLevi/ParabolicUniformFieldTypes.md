# Uniform field types distinguish actual parabolic quotient components

This internal module packages the uniform rational field-conjugacy condition
appearing in `RelativeParabolicEtaleLocalFiniteTypesStatement` and derives
disjointness of the actual affine quotient components. It does not prove
existence of such a family of types.

For subgroup inclusions `j a` over a scheme `S`,
`HasUniformParabolicFieldTypes` means that at every field-valued point `x`, every
parabolic subgroup of the actual group `G_x` is rationally conjugate to exactly
one of the base changes of the `j a`. All field extensions and all test-scheme
values of the subgroup ranges are retained.

When `G` is reductive and the `j a` are relative parabolic,
`conjugateParabolic_index_eq_of_fieldTypes` shows that equality of two actual
conjugate families over a field forces equality of their indices. The proof
composes both conjugates with the inverse of the second inner automorphism.
The resulting rational conjugacy and the identity conjugacy give two indices
for one field parabolic, so the uniqueness hypothesis identifies them.

For an affine base, `restrict_affineParabolicQuotientFamilies_comp` supplies the
group-lift evaluation formula for each actual quotient family.
`affineParabolicQuotientFamilies_disjoint_of_fieldTypes` treats arbitrary test
schemes. If the test is nonempty, two successive pullbacks of the surjective
quotient projections produce a nonempty scheme on which both parameters lift
to group-valued points. Equality of the families then becomes equality of their
actual conjugates. Restricting to the residue field at a point of that scheme
allows application of the preceding field criterion. On an empty test no index
equality is asserted.

For a finite index type, `finiteAffineParabolicChart_mono_of_fieldTypes` applies
this disjointness result to the previously constructed smooth proper quotient
coproduct chart. Its conclusion is monicity, with no surjectivity or
representability conclusion. The results are derived from the imported Library
constructions and the explicit uniform field-types premise; no new source
translation is claimed.
