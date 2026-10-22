# Character twists of smooth parts and smooth contragredients

Worker 4 constructs two representation equivalences for a commutative ring
`R`, a topological group `G`, an `R`-module `V`, a character
`chi : G →* Rˣ`, and an explicit open-kernel hypothesis on `chi`.
The coefficient ring, group and module inhabit independent universes.
The ambient representation need not be smooth or admissible, and the
module has no topology, dimension, freeness or finiteness hypothesis.

`smoothPartTwistEquiv chi rho hchi` identifies
`smoothPart (twist chi rho)` with `twist chi (smoothPart rho)`.
The smooth submodules can have different subtype descriptions, so this
is a bundled representation equivalence. Both its forward and inverse
maps retain the same vector of `V`. The published
`isSmoothVector_twist_iff` supplies the two membership proofs. Linearity,
inverse laws and equivariance follow directly from the retained vector
and the definitions of the restricted and twisted actions.

`smoothContragredientTwistEquiv chi rho hchi` identifies the smooth
contragredient of `twist chi rho` with the inverse-character twist of the
smooth contragredient of `rho`. Both maps retain each underlying linear
functional. The published `dual_twist` identifies the full algebraic
dual action with `twist chi⁻¹ rho.dual`. The character and its inverse
have the same kernel, as proved locally by extensionality. The published
smooth-vector twist equivalence therefore proves that the retained
functional is smooth in both directions. The same algebraic dual identity
proves equivariance. The inverse character is essential: the dual action
evaluates the original representation at the inverse group element.

All construction fields are proved. The private kernel equality is
implementation support for this construction. No project axiom, choice
of a new representation model, compact averaging, biduality, or
irreducibility theorem is assumed. These equivalences do not identify
the whole algebraic dual with its smooth subspace.

## Provenance and published inputs

This is an internal construction from the following published Library
interfaces, checked at commit
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`:

- `smoothVectors`, `smoothPart`, and `smoothMap` in
  `Langlands.Representation.Smooth.SmoothPart.Definitions`.
- `SmoothDual` and `smoothContragredient` in
  `Langlands.Representation.Smooth.Contragredient.Definitions`.
- `twist` in `Langlands.Representation.Twist.Definitions`.
- `dual_twist` in `Langlands.Representation.Twist.DualProof`.
- `isSmoothVector_twist_iff` in
  `Langlands.Representation.Twist.SmoothProof`.

The imported project source and Markdown files match the current Library.
The construction derives the compatibility directly from these results;
it does not attribute a new generalized theorem to external literature.
The topological-group assumption is needed for the existing smooth-part
and smooth-contragredient actions. Character continuity is not a premise:
the open kernel is stated explicitly.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development check `91e75698-7d2c-4a7e-869c-89cd9c793a4d` compiled
the pair without errors or warnings and inspected the selected definition.
Its three independent universes are retained; its only assumptions beyond
the explicit parameters are the standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`. The Lean source and all imported
project pairs remain unchanged since that check.
Compilation is development evidence; independent semantic review and
publication are required.
The full local Langlands correspondence remains unproved.
