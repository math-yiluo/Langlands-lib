# Smoothness under continuous complex twists

`Langlands.ContinuousComplexTwistSmoothCompatibility` states the following.
For a group `G` with a topology and a complex module `V`, assume Mathlib's
`NonarchimedeanGroup G`. Given a continuous homomorphism `chi : G →* ℂˣ`
and any representation `rho : Representation ℂ G V`, a vector is smooth
for `twist chi rho` if and only if it is smooth for `rho`. Consequently,
the twisted representation is smooth if and only if the original is.

The nonarchimedean instance is explicitly quantified inside the proposition.
It includes the topological-group laws and the open-subgroup neighborhood
basis at the identity. The complex units carry their usual topology.
The group and module have independent carrier universes. The module has
no topology, and the representation is not assumed continuous or smooth.
There are no local compactness, separation, unitarity, admissibility or
finite-dimension hypotheses. An instance for a concrete p-adic group is
a separate obligation.

## Provenance and exact dependencies

This is an internal corollary of two independently accepted results.
The open-kernel theorem applies to the continuous complex character;
the open-kernel twist theorem then gives the two asserted equivalences.
This statement removes the explicit open-kernel premise in the complex
nonarchimedean setting. It is not a new definition of smoothness or a
redefinition of either accepted target.

The statement imports the following accepted definition pairs, version 1:

- `Langlands.Representation.Twist.Definitions`, artifact
  `c83db975-8b79-4fbb-9901-2db836910a0a`, published at
  `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
- `Langlands.Representation.Smooth.Definitions`, artifact
  `665022df-625b-44ae-9dbd-425f6e266bab`, published at
  `10c81beaaff024987cf2945c64d0c9511f6cb686`.

The derived provenance uses these exact accepted proof results, version 1:

- `Langlands.isOpen_ker_of_continuous_complex_character` in
  `Langlands.Representation.Twist.ContinuousCharacterProof`, artifact
  `3d3e21f0-1699-49c7-a6a5-131a90921939`, published at
  `d0f5322f745425b08ae8e72c1031206f45cb049e`.
- `Langlands.isSmoothVector_twist_iff` and `Langlands.isSmooth_twist_iff`
  in `Langlands.Representation.Twist.SmoothProof`, artifact
  `bfc0af4a-747e-42b0-befc-a12ca0239b22`, published at
  `46286695a6510ca7bbbdf374984d46caeb0f43d0`.

The statement itself imports neither proof module. The paired proof
module performs the composition. The full final review and effective
source closure of the new open-kernel proof were checked before reuse;
the current smoothness proof and definition source hashes also match.
The general corollary is internal, rather than an attributed theorem
from the motivating local Langlands literature.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 4 authored this statement. It is a proposition definition awaiting
independent review and publication, not itself a proof or an LLC claim.
