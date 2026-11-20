# The universal closed stabilizer of a finite identity-jet subscheme

For a smooth separated group over an affine base, each identity jet is a finite,
flat, locally finitely presented scheme. Its finite-flat subscheme parameter
classifies the closed flat, locally finitely presented subschemes of that jet
on every test scheme. The pulled-back jet embeds as a closed subscheme of the
pulled-back group, so the universal ideal defines an actual closed subscheme of
the group over the parameter. This universal closed family is again finite,
flat and locally finitely presented over the parameter. Closed stabilizer
descent gives a group scheme representing its conjugation stabilizer.

For any point of the parameter, the evaluated ideal is the pullback of the
universal ideal. The associated closed subscheme gives a pullback square over
the point. The canonical comparison of successive and direct pullbacks of the
group identifies the specialized universal stabilizer with the stabilizer of
this evaluated closed subscheme on all refinements of the test.

This implements the universal normalizer construction in Raynaud, SGA 3,
Exposé XV, proof of Lemma 5.3, Gille–Polo recomposed p. 266. The finite-flat
subscheme parameter here covers all ranks of the finite jet quotients.

Finiteness, flatness, and local finite presentation of the jet projection come from `IdentityJetFiniteProjection` and `IdentityJetSeparatedLocalBases`.
