# Functoriality and base change of actual identity jets

This module extends the Library's construction of actual identity jets.
A group homomorphism preserves the identity section, so the pulled-back
target identity ideal is contained in the source identity ideal. Pullback
preserves ideal powers, giving the induced map between the order-`n`
neighborhoods. The closed inclusions characterize the induced maps and
give the identity and composition laws of `IdentityJet.schemeFunctor`.

For a separated group scheme the identity section is a closed immersion.
Under any change of base its cartesian square identifies the pulled-back
identity ideal with the new identity ideal. Taking powers gives the
cartesian square of actual identity jets. If the group is locally of
finite type, its identity jet projection is finite. Applying base change
for affine pushforward to the jet's structure sheaf gives
`IdentityJet.separatedBaseChangeIso` for the actual jet module.

Conjugation by a test-valued point is an inner automorphism of the
base-changed group. The jet functor restricts this automorphism to
the actual identity neighborhood. `IdentityJet.baseChangedConjugationAut`
transports it through the cartesian comparison and gives a group
homomorphism to automorphisms of the pulled-back jet in the slice over
the test scheme. `IdentityJet.baseChangedConjugationAut_inclusion`
identifies its restriction along the closed inclusion with the
given inner automorphism.

This is an internal extension of the Library's affine-group base-change
construction and group-scheme inner automorphisms.
