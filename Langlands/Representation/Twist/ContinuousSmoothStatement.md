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

This is an internal corollary of two Library results.
The open-kernel theorem applies to the continuous complex character;
the open-kernel twist theorem then gives the two asserted equivalences.
This statement removes the explicit open-kernel premise in the complex
nonarchimedean setting. It is not a new definition of smoothness or a
redefinition of either target.

The statement imports the following definition modules:

- `Langlands.Representation.Twist.Definitions`.
- `Langlands.Representation.Smooth.Definitions`.

The derived provenance uses these exact proof results:

- `Langlands.isOpen_ker_of_continuous_complex_character` in
  `Langlands.Representation.Twist.ContinuousCharacterProof`.
- `Langlands.isSmoothVector_twist_iff` and `Langlands.isSmooth_twist_iff`
  in `Langlands.Representation.Twist.SmoothProof`.

The statement itself imports neither proof module. The paired proof
module performs the composition. The effective
source closure of the open-kernel proof was checked before reuse;
the smoothness proof and definition source hashes also match.
The general corollary is internal, rather than an attributed theorem
from the motivating local Langlands literature.

Environment: Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
It is a proposition definition, not itself a proof or an LLC claim. The proof
is `Langlands.continuousComplexTwistSmoothCompatibility`, in
`Langlands.Representation.Twist.ContinuousSmoothProof`.
