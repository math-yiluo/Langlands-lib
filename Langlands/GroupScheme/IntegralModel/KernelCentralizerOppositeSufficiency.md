# Opposite-factor sufficiency from the ambient residue quotient

This internal construction specializes the component-quotient opposite-factor
theorem to data from the original ambient integral model. It works at arbitrary
universe `u` over a Henselian discrete valuation ring with perfect residue field.
The ambient generic group is affine and the integral model is smooth.

The supplied integral torus is split. Its generic map into the ambient group is
monomorphic. The hypothesis `HasRelativeRootSystem` for this generic torus
map supplies the actual crystallographic root system, identification of its
Weyl group with the actual Weyl-action image, and faithfulness of that action.
The base change of the supplied character is an actual relative root. A supplied
cocharacter pairs positively with that character. The ambient special fibre has
a smooth homomorphism to an affine connected reductive group with full smooth,
connected, unipotent kernel. The original residue torus maps to a maximal split
torus there.

For the given integral section, its generic image lies in the actual root
subgroup and is nonidentity, and its image in the ambient residue quotient is
nonidentity. A prescribed opposite-factor pair for that same generic point is
retained. `integral_oppositeFactors_of_residueQuotient` proves both prescribed
factors integral. `residueQuotientOppositeFactorLift` chooses integral sections
with exactly those generic images.

The proof chooses the full character-kernel centralizer over the integral ring
and its actual relative identity component. It also chooses a smooth closed
representative of the residue centralizer for the original torus map and
character. Positive pairing makes the residue character nonzero, so the
identity component of this representative is connected reductive.
`fibreQuotientMap` supplies the actual component quotient, smooth scheme
surjectivity and its full smooth connected unipotent kernel. Its torus square
transfers maximality of the original residue torus. The full-character quotient
action supplies the required multiplicative-group action and its exact
restriction to torus conjugation.

The generic identification of the integral model transports the root membership
back to the actual generic fibre. `integralRootUnipotentLift` then chooses an
integral dynamic-unipotent point in the component mapping to the original
section. Naturality of reduction and the ambient quotient square detect its
nonidentity in the component quotient. The component-quotient opposite-factor
theorem now applies with the original section and prescribed pair.

The provenance is internal composition of the imported constructions. No
component quotient, action, centralizer data or integral root lift is assumed
as an additional premise. The hypotheses about the ambient model, quotient,
torus and positive cocharacter remain explicit; this unit does not construct
the fixed-point integral model or prove the full host statement.
