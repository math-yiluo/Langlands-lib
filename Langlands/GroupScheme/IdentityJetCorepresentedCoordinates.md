# Actual jet sections in a supplied corepresenting algebra

For a group-valued functor over a commutative ring `R` with supplied
corepresenting algebra `B`, this module identifies its truncated coordinate
algebra with sections of the actual identity neighborhood after every base
change `b : S → Spec R` and over every affine open `U` of `S`.

`corepresentedCoordinateEquiv` compares `B` with the existing chosen affine
coordinates of the actual corepresented group. Full faithfulness of relative
spectrum constructs it from the actual group-scheme isomorphism.
`spec_corepresentedCoordinateEquiv` records its exact spectrum map. The actual
identity-section naturality law then proves counit compatibility.

`corepresentedJetCoordinateEquiv` passes this comparison to the quotients by
the `(n+1)`st powers of the augmentation ideals. The kernel of the counit is
transported by the algebra equivalence; powers commute with this transport.
`corepresentedBaseChangeJetEquiv` extends coefficients to `Γ(S,U)` and uses the
existing actual base-changed jet comparison. Thus it is an equivalence
`Γ(S,U) ⊗_R (B/aug^(n+1)) ≃ Γ(IdentityJet.module G_S n,U)`.

The theorem `corepresentedBaseChangeJetEquiv_tmul_mk` gives the exact formula:
`a ⊗ class(c)` maps to `a` times restriction to the actual jet of the function
obtained by pulling `c` back along the actual pullback projection `G_S → Spec B`.
This formula uses the supplied coordinates, with no unspecified change of
basis. The auxiliary general formulas `coordinateMap_comp_specMap` and
`restrict_quotientCoordinates_mk` are literal function substitution and
restriction laws.

This is an internal consequence of the imported actual affine-coordinate,
counit, quotient, tensor-product, and actual identity-jet APIs. It imposes no
smoothness, flatness, or finite-presentation hypothesis. It does not assert
conjugacy or equality with a classified Grassmannian kernel.
