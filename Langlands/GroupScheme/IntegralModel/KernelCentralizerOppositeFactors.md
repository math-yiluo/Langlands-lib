# Opposite factors from an actual component quotient

This internal assembly uses the actual full character-kernel centralizer and its
relative identity component in an integral model over a Henselian discrete
valuation ring with perfect residue field. The integral split torus, character,
positive cocharacter, ambient section, and prescribed opposite-factor pair are
retained. The ambient generic group is affine, and its generic torus map `iK`
is monic.

The theorem takes a smooth surjective quotient of the actual component special
fibre onto a connected reductive group, with connected unipotent kernel. It also
takes maximality and monicity of the original split torus in that quotient, and
a multiplicative-group action whose restriction through the full character is
the original torus conjugation. An integral dynamic-unipotent point in the
component must map to the given ambient section, and its quotient reduction must
be nonidentity. The ambient generic torus map is supplied with
`HasRelativeRootSystem iK`: this includes the actual crystallographic root
system, identification of its Weyl group with the actual Weyl-action image,
and faithfulness of that action. The ambient generic character `aK` is an
actual relative root, and the generic image of the given section belongs to
its root subgroup and is nonidentity. A prescribed opposite-factor pair is
supplied for that same point.

The implemented proof base changes the canonical dynamic-unipotent inclusion
and applies functoriality to put its quotient reduction in the positive dynamic
subgroup. Nonidentity proves this subgroup is nontrivial. The Henselian
reflection-cell construction gives one integral character-negating normalizer
and translated opposite-cell coordinates for both the component point and its
inverse. Actual cell coordinates map to the ambient model through the two
specified centralizer inclusions. The ambient reflection construction certifies
the same generic normalizer as the relative reflection for the actual root.
The supplied root-system and faithful Weyl-action comparison identifies its
reflection class with that of the prescribed pair. The
prescribed-opposite-factor integrality theorem then proves that both members
of the original factor pair are integral.

`componentQuotientOppositeFactorLift` chooses integral sections with exactly
those two prescribed generic images from the proved integrality conclusion.

This result is derived from the imported reflection lifting, cell transport,
and prescribed-factor theorems. It assumes the component residue quotient and
its action and geometry; it does not construct them or prove the host
depth-zero opposite-factor statement.
