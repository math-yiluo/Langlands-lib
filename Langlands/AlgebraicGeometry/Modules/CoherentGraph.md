# Coherent graphs on affine opens

This internal prerequisite constructs the actual pullback graph of an isomorphism
between restrictions of two module sheaves. It is intended for coherent support
induction in the Euler-polynomial proof. The common pushforward target is not
required to have finite affine sections.

The support lemmas use actual abelian stalks and restriction-stalk isomorphisms.
Tensoring with a locally free rank-one sheaf preserves stalk support, by local
trivialization of the tensor product. Thus it preserves the closed support-height
bounds in `SupportDimension`.

Pullbacks of quasi-coherent module sheaves are quasi-coherent: the pullback is the
kernel of the difference map out of their binary direct sum. On a locally
noetherian scheme, finite affine sections pass to the pullback as a submodule of
that sum. The graph projections become isomorphisms upon restriction to the
chosen open, by preservation of pullbacks and the restriction-adjunction unit.

These are internal consequences of the module restriction and abelian category
APIs, not an assumed Euler polynomial or positivity certificate. The full
geometric induction and leading-term assertion remain separate obligations.
