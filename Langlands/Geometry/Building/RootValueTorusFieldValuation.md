# Original-point shifts and conditional torus-then-field valuation assembly

This internal unit assembles the already proved scalar laws of the actual
`torusFieldRestrictedRootFunctionFamily`. All fields, groups, torus maps
and upper valuation are unchanged from `RootValueTorusFieldAxioms`. Here
the original map `i:S→G` is monomorphic. The actual factorization through
the upper split torus remains `groupHom f ≫ j = i_K`.

`TorusFieldOriginalPointShifts` is a proposition about the canonical
torus-restricted family over `K`: for each **original** normalizer point,
there exists an original real cocharacter shift whose formula holds on
scalar extensions of original actual root-group points. It does not test
all lower-torus root-group points over `K`. No claim that original
normalizer points preserve the chosen upper torus is made.

`torusFieldOriginalPointShifts_iff` proves this is exactly the condition
that every original normalizer acts on the entire original restricted
family by a real cocharacter translation. The proof uses the established
support normalization and `fieldRestrict_smul_eq_vadd_iff`.
`torusFieldRestrictedRootFunctionFamily_reflection_of_originalPointShifts`
then derives the original V2 reflection formula by the generic
original-point shift theorem. The reflection constant is determined by
the chosen shift; no valuation for the lower torus over `K` is assumed.

`torusFieldRestrictedValuationOfOriginalPointShifts` constructs a subtype
element with exactly the unchanged original family. It uses the proved
normalization, V0, V1, V3 and V4, the just-derived V2, and an explicit
remaining premise giving precisely original V5 on the original factors.
V3 uses original as well as upper opposite factor pairs. V0 retains upper
unit-character compatibility and nontriviality on original units.

The two remaining structural obligations are the original-point shift
condition and original V5. This conditional constructor proves neither,
and does not prove adapted existence, initial existence, building
geometry or the supplied-model comparison. Its provenance is assembly
of the implemented scalar and commutator results with the generic actual
field-shift criterion.
