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
subgroup with the kernel. The cofinal admissibility criterion
and the smooth-twist theorem then give the second assertion.
This is not an attributed theorem from an external source.

The statement imports these definition modules:

- `Langlands.Representation.Twist.Definitions`.
- `Langlands.Representation.Smooth.Definitions`.

The derived proof uses these proof modules:

- `Langlands.Representation.Twist.SmoothProof`.
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`.

The statement does not import either proof module. All four dependencies
were verified with matching source hashes and no unavailable dependencies.
Mathlib supplies the Noetherian predicate.

Environment: Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The proof is `Langlands.twistAdmissibilityCompatibility`, in
`Langlands.Representation.Twist.AdmissibilityProof`; no local Langlands
correspondence is asserted.
