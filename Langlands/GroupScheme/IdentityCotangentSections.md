# Actual affine identity-cotangent sections and the augmentation quotient

Let `G` be a group scheme over an arbitrary base scheme `S`, with affine
structure morphism. For an affine base open `U`, put
`R = Γ(S,U)`, `A = Γ(G.total, G.projection⁻¹(U))`, and let `ε : A →ₐ[R] R`
be the actual identity evaluation `IdentityJet.augmentation G U`.
The preimage of `U` in the group is affine.

This is an internal composition of the actual affine differential-section
comparison, the actual pullback tensor map, and the canonical algebraic
augmentation-cotangent/Kähler equivalence. It adds no external source claim.

`augmentationAlgebra` installs the `A`-algebra structure on `R` given by
the actual identity. `augmentationScalarTower` verifies that its composite
with the actual base algebra map is the identity, by the augmentation's
algebra-homomorphism law.

`differentialSectionsEquiv G U` is the `A`-linear equivalence between
sections of the actual relative differential sheaf above `U` and
`KaehlerDifferential R A`. It uses
`relativeDifferentialsSectionsIso` and explicitly transports its
algebra structure from `appLE` to the actual group structure map's
section algebra. `projection_appLE_self` proves the required equality.

For quasi-coherent relative differentials,
`pullbackSectionsEquiv G U` is the `R`-linear equivalence

`R ⊗[A] Γ(relativeDifferentials G.projection, G.projection⁻¹(U))
  ≃ Γ(G.cotangentAtIdentity, U)`.

Its forward map is exactly the actual affine pullback tensor map for
the identity section. `pullbackSectionsEquiv_one_tmul` computes it as
the actual section pullback on tensors with coefficient one.
`smoothDifferentials_isQuasicoherent` supplies the required
quasi-coherence when the structure morphism is smooth, using the
proved finite local bases of smooth differentials.

`sectionsEquiv hG U` is the resulting `R`-linear equivalence

`Γ(G.cotangentAtIdentity, U) ≃ (ker ε).Cotangent`.

The actual cotangent sheaf is, by definition, the pullback of the actual
relative differential sheaf along the identity. The construction first
inverts the affine pullback tensor map, then applies scalar extension
to `differentialSectionsEquiv`, and finally inverts the canonical
augmentation-cotangent/Kähler tensor equivalence.

`sectionsEquiv_pullback_model_D` computes this map on the pullback of
the model section corresponding to an algebraic differential `d(a)`:
the result is precisely `AugmentedAlgebra.classMap ε a`.
The proof uses the explicit tensor pullback computation, cancels
the two equivalences, and applies the inverse Kähler tensor formula.

The result holds for every smooth affine group scheme over an arbitrary
base, in every universe. There is no field, domain, noetherian or
constant-rank hypothesis. Compatibility with restriction to smaller
affine opens and determinant-line gluing remain separate work.
