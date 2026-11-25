# Residue-identity naturality of the fixed-frame base-change comparison

This module proves that the direct fixed-frame test comparison commutes
with the actual identity-frame maps forced by equal stored residue maps. It
derives from complete formal coordinate equations and scalar transport; no
new literature assertion is made.

`globalFrameIso_hom_coordinates` eliminates equality of the stored residue
maps and retains the actual integral identity formal map.
`globalFrameIso_map_hom_coordinates` shows its complete series remain identity
on any coefficient test. Scalar equality transport retains that series.

`baseChange_residue_eq` composes the two equal stored maps with the actual
induced quotient scalar map. `baseChangeNewResidueFrameTestIso` is the identity
comparison forced by this new equality, evaluated on the new test algebra.
`baseChangeResidueFrameTestIso` evaluates the original forced identity on the
restricted test algebra and transports its scalar structure to the new one.
Neither map chooses a fixed-frame automorphism.

`baseChangeGlobalFrameTestIso_residue_natural` proves equality of the two
integral formal routes around the square formed by these identity-frame maps
and the two direct fixed-frame base-change comparisons. Each constituent has
complete identity coordinate series, so both routes have the same actual
forward formal map. Actual inverse uniqueness determines the whole
isomorphism. This is formal-map equality, not point-evaluation equality.

`baseChangeResidueFrameSquare` rationalizes these four actual full-order maps
and packages their proved equation in the existing quasi-isogeny commuting
square structure. Rationalization preserves the integral compositions.

The parameters retain the local field, finite-dimensional central division
algebra, embedded field, coefficient and residue fields, fixed height-certified
frame and Nilp objects in universes `{v,u}`. Both framed representatives have
the given equal residue maps; their targets and covers may differ and need not
be finite. No target chart enters the fixed-frame square. Preservation of the
full original framed comparison square, comparison-class functoriality,
actions and representability are outside this module; the first two are
`framingSquare_baseChange` in `DrinfeldFramedComparisonBaseChange` and the
functor of `DrinfeldFramedClassFunctor`, and actions and representability
remain separate.
