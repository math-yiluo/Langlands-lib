# Smooth Lie base change: identity and composition

For a smooth group scheme over an arbitrary base, this internal construction
packages two successive instances of `smoothLieBaseChangeIso` as the isomorphism
`smoothLieBaseChangeCompIso`. Smoothness of the first base change follows from
stability of smooth morphisms under base change.

The identity law states that the actual Lie base-change comparison followed by the
Lie differential of `baseChangeIdIso.hom` is the module identity pullback comparison.
The composition law states that successive Lie comparisons, followed by the Lie
differential of `baseChangeCompIso.inv`, equal the module pullback composition
comparison followed by the Lie comparison for the composite base map. Equivalently,
the sequential comparison is the composite-base route followed by the Lie
differential of `baseChangeCompIso.hom`.

The proofs dualize the actual cotangent identity and composition laws, use the
characterization of the smooth Lie comparison by the cotangent map, and cancel
invertible dual cotangent maps. Naturality and the identity/composition laws of
the canonical dual-pullback comparison supply the required intermediate equalities.

All formulas hold in an arbitrary universe and for arbitrary base morphisms.
There are no reductivity or commutativity hypotheses. These are coherence results
for the established smooth Lie comparison and do not prove parabolic
representability.
