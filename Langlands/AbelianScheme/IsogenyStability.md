# Proof of stability of relative isogenies

`Langlands.GroupScheme.isogenyStability` proves the exact proposition
`Langlands.GroupScheme.IsogenyStabilityStatement`. The file also exposes its
three components as `isIsogeny_id`, `IsIsogeny.comp`, and
`IsIsogeny.baseChange`.

The proof constructs `ContainsIdentities`, `IsStableUnderComposition`, and
`IsStableUnderBaseChange` instances for `isogenyProperty` by applying Mathlib's
corresponding results to the scheme-morphism predicates `IsFinite`,
`Flat`, and `Surjective`. The composition component for surjectivity uses
composition of the underlying surjective functions directly. It applies `id_mem` and `comp_mem` to the underlying scheme
morphisms. For base change it applies `overPullbackMap` to the underlying
morphism over the base. The underlying scheme morphism of the induced group
homomorphism is definitionally the morphism used by that theorem.

The final theorem packages these three proofs into the conjunction defining
the published target. No additional geometric hypotheses or axioms enter.
This is an internal proof from the imported definition, statement, and
Mathlib's morphism-property API.
