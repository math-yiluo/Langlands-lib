# Scalar residue criterion for structure-module stalks

The theorem `unitEndResidueStalkCriterion` proves the derived internal statement
`UnitEndResidueStalkCriterion` for arbitrary schemes in universe `u`. The helper
`unitEnd_stalkIso_iff_residue_ne_zero` gives its pointwise form. The stalk here is
the actual underlying abelian-group stalk, and the residue value is the scheme's
actual `Γevaluation` of the endomorphism's global value at one.

Every structure-module endomorphism acts on sections by multiplication by its
value at one. These values commute with restrictions. For the forward implication,
the published `isOpen_unitEnd_stalkIso` supplies the open locus of invertible
stalk maps. On that open, `isIso_iff_stalk_isIso` makes the restricted morphism an
isomorphism. Surjectivity on top sections makes its scalar a unit. The scalar's
germ is then a unit, so `IsLocalRing.residue_ne_zero_iff_isUnit` makes its residue
nonzero.

Conversely, that same local-ring equivalence turns a nonzero residue into a unit
germ. Mathlib's `RingedSpace.isUnit_res_of_isUnit_germ` supplies an open
neighborhood where the scalar is a unit. Naturality propagates the unit to each
smaller open. Multiplication by this unit is bijective on sections, so the
restricted module morphism is an isomorphism. The published
`isIso_stalk_restrict_iff` transports this to the original stalk.

This is an internal scalar step toward `LineBundleResidueStalkCriterion`; it does
not assert the comparison with the actual pullback section for an arbitrary line
bundle. The local multiplication and restriction arguments adapt Worker 311's
published `LineBundleFrameOpen` proof. Its openness theorem and the published
`SectionLocusComparison` are imported without modification. No additional
mathematical hypotheses or axioms are introduced.
