# Compatibility of the canonical pullback tensor comparison

`Langlands.Scheme.Modules.pullbackTensorCompatibility` proves exactly
`Langlands.Scheme.Modules.PullbackTensorCompatibilityStatement.{u}` in arbitrary
universe `u`, without additional hypotheses. Its three constituents are also
available as `pullbackTensorIdentity`, `pullbackTensorComposition`, and
`pullbackTensorSymmetry`.

The imports are `PullbackTensorCompatibilityStatements` and
`PullbackUnitProofs`; the latter supplies the shared adjunction helper.
All maps are the fixed maps in that statement: `pullbackTensorComparisonApp`,
`Scheme.Modules.pullbackId`, `Scheme.Modules.pullbackComp`, and the explicit
`tensorComm`. The local monoidal and symmetric instances are the existing
sectionwise structures on **presheaves** of modules. The proof supplies no
monoidal instance on pullback or on module sheaves and assumes no tensor
comparison invertibility.

## Proof mechanism

Write `F_f` and `R_f` for pullback and pushforward, `δ_f` for the canonical
pullback tensor comparison, `μ_f` for `pushforwardTensorApp`, and `a♯` for the
adjoint of a map `a` under `F_f ⊣ R_f`. The private lemma `adjoint_tensor`
proves

`(δ_f ≫ tensorMap a b)♯ = tensorMap a♯ b♯ ≫ μ_f`.

It uses the published adjunction characterization of `δ_f`, naturality of
`μ_f`, and functoriality of `tensorMap`. The private
`adjoint_composite_tensor` applies this formula twice, using the hom-set
equivalence of the composite adjunction. The resulting map is the tensor of
the two composite adjoints, followed by `μ_g` and `R_g.map μ_f`.

The three pushforward calculations are proved by injectivity of
`tensorHomEquiv`, then by extensionality of presheaf morphisms and pure-tensor
extensionality on each open set. The identity pushforward comparison is
sectionwise the identity, so its tensor equation is definitional. For
composition, evaluation of `tensorHomEquiv_pushforwardTensorApp f P Q` at the
inverse image of an open under `g` identifies the two paths; the pushforward
composition comparison again has identity components. For symmetry,
naturality of the sheafification unit with respect to the presheaf braiding
identifies both paths with swapping the two sections and then sheafifying.

## Identity, composition, and symmetry

For identity, Mathlib's `unit_conjugateEquiv` and
`Scheme.Modules.conjugateEquiv_pullbackId_hom` identify the adjoint of
`(pullbackId X).hom.app T` with `(pushforwardId X).inv.app T`.
Applying the pullback hom-set equivalence to the required equation, the
`adjoint_tensor` formula therefore reduces it to the pushforward identity
calculation.

For composition, the shared `homEquiv_conjugate` adjunction lemma says that precomposition
with a transformation between left adjoints corresponds to postcomposition
with its conjugate between right adjoints. With
`Scheme.Modules.conjugateEquiv_pullbackComp_inv`, it shows that the composite
adjoint of `(pullbackComp f g).hom.app T`, followed by
`(pushforwardComp f g).hom.app (F_(f ≫ g).obj T)`, is the unit of the adjunction
for `f ≫ g`. Cancellation of the pullback composition isomorphism reduces
the desired equation to one starting at `F_(f ≫ g)(M ⊗ N)`. After applying
its hom-set equivalence, the composite adjoint formula and pushforward tensor
composition calculation reduce both sides to the tensor of the two units,
followed by `μ_(f ≫ g)`.

For symmetry, applying the pullback hom-set equivalence turns the pulled-back
swap into precomposition with `tensorComm`. The pushforward symmetry
calculation and naturality of `tensorComm` against the two adjunction units
then give equality. This naturality follows by applying sheafification to
naturality of the presheaf braiding.

## Provenance and scope

This is an internal categorical proof of the published compatibility targets,
using their existing sheaf-theoretic constructions. It makes no claim to
translate a separate literature proof. The `homEquiv_conjugate`
calculation is reused from [PullbackUnitProofs](PullbackUnitProofs.md),
whose identity/composition proof supplied the model for using Mathlib's
adjunction mates. The shared `tensorComm_naturality` lemma is available from
[Tensor](Tensor.md); its proof was moved unchanged from
[RigidifiedTensorSymmetry](../Picard/RigidifiedTensorSymmetry.md). The rest of the argument derives the tensor-specific
formulas from `PullbackTensor` and the pinned Mathlib adjunction and presheaf
APIs. The transparency option exposes existing scheme-module wrappers to
elaboration; it adds no mathematical assumption.

The result establishes precisely identity, composition, and explicit symmetry
compatibility. Tensor invertibility, unitor and associativity laws, comparison
with the localized monoidal structure, and assembly of a strong symmetric
monoidal pullback functor are outside this theorem.
