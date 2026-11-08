# Unitary twist closure of actual relative witnessed generators

This internal interface names the precise twist closure used in the relative
isometry operation proof. It was first expressed in the private isometry
assembly draft and is derived directly from the existing witnessed generators
and the two lattice equivalences in the published operation target.

`Langlands.Global.PoleComparison.RelativeWitnessedTwistClosure` means that
every actual relative witnessed generator has another actual generator whose
Weil element is its twist by the pullback of the supplied local character and
whose automorphic element is its determinant-character twist. Both generators
have the original field, Weil-carrier and presentation-factor universes.
The predicate makes no choice of an isometry and asserts no closure by itself.

`relativeWitnessedTwistClosure_of_globalInputs` proves this predicate from
proofs of the actual cuspidal determinant-multiple statement, its presented
association statement, and local transfer reciprocity, together with an
arithmetic class-family certificate and unitary character extension at the
given field and finite place. Its extension premise uses the natural
completion topology. Its character and reciprocity-candidate arguments are
exactly those of the published operation target, including an arbitrary
modulus-one character and any candidate satisfying geometric reciprocity.

The proof introduces an original generator and applies the proved
`WitnessedGenerator.exists_unitaryCharacterTwist`. That theorem constructs a
complete generator with both required lattice identities and handles the
comparison between the natural completion topology and the canonical p-adic
topology. No further transport or choice is needed here.

This is a composition of inspected internal definitions and a proved
conditional construction; it makes no additional literature assertion.
All global existence and comparison statements remain explicit proof inputs.
In particular this module does not prove
`RelativeIsometryOperationStatement`. Applying this deduction in the final
proof still requires discharging each input with a proved result.
