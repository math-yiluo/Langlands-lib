# Admissibility under character twists

`Langlands.TwistAdmissibilityCompatibility` has two related assertions.
For a commutative ring `R`, group `G`, `R`-module `V`, character
`chi : G →* Rˣ`, representation `rho`, and subgroup `H ≤ chi.ker`,
the submodules `fixedVectors (twist chi rho) H` and `fixedVectors rho H`
are equal. This assertion has no topology or Noetherian hypothesis.

For any topology on `G`, assume additionally that `R` is Noetherian and
the kernel of `chi` is open. Then `twist chi rho` is admissible if and
only if `rho` is admissible. The topology and Noetherian instances are
explicitly quantified inside the second conjunct of the proposition.
The coefficient ring, group, and module retain independent universes.
No topology on the module, topological-group laws, local compactness,
separation, dimension bound, or continuity of the character is assumed.

Admissibility uses the existing `Langlands.IsAdmissible`: smoothness
together with finite generation of fixed-vector modules for **every**
open subgroup. The Noetherian hypothesis supports passing finite
generation to a submodule when comparing different fixing subgroups;
it is not imposed on the first, purely algebraic assertion.
An open kernel is a stated hypothesis, not an inferred continuity fact.

## Provenance and exact dependencies

This is an internal derived result. On a subgroup in the kernel, the
scalar twist acts by the same operators. If the kernel is open, the open
subgroups it contains form a downward-cofinal family: intersect any open
subgroup with the kernel. The accepted cofinal admissibility criterion
and accepted smooth-twist theorem then give the second assertion.
This is not an attributed theorem from an external source.

The statement imports these accepted definition artifacts, version 1:

- `c83db975-8b79-4fbb-9901-2db836910a0a`,
  `Langlands.Representation.Twist.Definitions`, published at
  `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
- `665022df-625b-44ae-9dbd-425f6e266bab`,
  `Langlands.Representation.Smooth.Definitions`, published at
  `10c81beaaff024987cf2945c64d0c9511f6cb686`.

The derived proof uses these accepted proof artifacts, version 1:

- `bfc0af4a-747e-42b0-befc-a12ca0239b22`,
  `Langlands.Representation.Twist.SmoothProof`, published at
  `46286695a6510ca7bbbdf374984d46caeb0f43d0`.
- `44ec0cb2-5236-4d2c-bd05-2924d52ec404`,
  `Langlands.Representation.Smooth.Admissibility.CofinalProof`, published at
  `d02f4b7f1571e734196137adc2dd6a47a8103ac5`.

The statement does not import either proof module. All four dependencies
were verified accepted, published, and current at Library commit
`5bc58c2525e0499012801c80f17b6a9c04d57263`, with matching source hashes
and no unavailable dependencies. Mathlib supplies the Noetherian predicate.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 4 authored this proposition definition. Independent statement
review and publication are still required; no local Langlands
correspondence is asserted.
