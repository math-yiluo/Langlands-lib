# Actual parabolic identity-jet tensor quotients

This internal specialization uses the actual ambient coordinate and jet APIs
and the published closedness of relative parabolic subgroups. Let `G` be
reductive over `Spec R`, let `M` be any scheme over `Spec R`, and let `r` be
any actual representative of a relative parabolic subgroup functor of `G_M`.

`ParabolicRepresentative.identityJetTensorCoordinates hG r n U` is the actual
map from `Γ(M,U) ⊗[R] (B/I^(n+1))` to sections over `U` of
`IdentityJet.module r.group n`, where `B` is the fixed coordinate algebra of
`G` and `I` is its counit kernel. It is precisely
`IdentityJet.ambientTensorCoordinates` for the actual inclusion `r.hom`.
The base algebra structure is induced by the actual morphism `M → Spec R`.
The representative's relative parabolicity supplies affineness of its
structure morphism.

`identityJet_inclusion_isClosedImmersion` obtains closedness from
`relativeParabolicClosed` applied to the reductive base change `G_M`.
`identityJetTensorCoordinates_surjective` then applies the ambient tensor
surjectivity theorem. There is no extra smoothness, noetherian, or
finite-type hypothesis on the coefficient ring or the parameter scheme.

`identityJetTensorQuotientEquiv` is the induced linear equivalence from
the tensor module modulo the kernel of this actual map to actual jet
sections. It uses the first isomorphism theorem and the preceding
surjectivity. `homogeneousQuotientIdentityJetTensorQuotientEquiv` applies
it to the chosen actual representative of
`homogeneousQuotientParabolic hG i hi Q` on any supplied homogeneous
quotient `Q`.

The kernel here is defined by restriction to the actual parabolic identity
neighborhood. This result makes no comparison with the kernel of the
Grassmannian quotient and makes no determinant ampleness assertion.
