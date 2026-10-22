# Coherence of the canonical pullback unit

`Langlands.Scheme.Modules.pullbackUnitCoherence` proves
`Langlands.Scheme.Modules.PullbackUnitCoherenceStatement` from
`Langlands.AlgebraicGeometry.Modules.PullbackUnitStatements`. The theorem
combines the adjunction characterization, identity compatibility, and composition
compatibility of the canonical comparison `f^* O_Y ≅ O_X`, for all schemes and
morphisms in an arbitrary universe `u`.

The proof follows the existing adjunctions and their comparison maps in pinned
Mathlib. It is internal categorical reasoning; it does not claim to reproduce
a literature proof.

`pullbackUnitAdjunction` is the inverse law for the hom-set equivalence, because
the comparison was defined as the adjoint of the structure-sheaf morphism.

`pullbackUnitIdentity` applies injectivity of the hom-set equivalence. Mathlib's
`unit_conjugateEquiv` and `Scheme.Modules.conjugateEquiv_pullbackId_hom` identify
the adjoint of the identity comparison with the inverse pushforward identity
comparison. At the structure sheaf its component is definitionally the
structure-sheaf map for the identity scheme morphism.

For composition, two private general lemmas keep the categorical calculations
independent of scheme wrappers. `homEquiv_conjugate` says that precomposing with
a natural transformation between left adjoints corresponds to postcomposing
with its conjugate between right adjoints. It follows from the adjunction unit
formula and naturality. `homEquiv_comp_map` computes the hom-set equivalence of
a composite adjunction on a composite involving a mapped morphism, using the
composition formula and naturality of each hom-set equivalence.

`pullbackUnitComposition` applies these lemmas and the two adjunction
characterizations to the unit maps. Mathlib's
`Scheme.Modules.conjugateEquiv_pullbackComp_inv` identifies the conjugate of the
inverse pullback composition comparison with the forward pushforward
composition comparison. The resulting equality of maps from `O_Z` into
`(f ≫ g)_* O_X` holds by definitional equality of the structure-sheaf maps.
Injectivity of the hom-set equivalence and cancellation of the comparison
isomorphism give precisely the stated composition equation.

The local transparency settings only expose the existing scheme-module
wrappers to elaboration. This proof introduces no assumptions on the schemes
or morphisms and no tensor or monoidal instance. It establishes exactly the
three unit-comparison laws, leaving the broader tensor and monoidal obligations
to their own constructions and proofs.
