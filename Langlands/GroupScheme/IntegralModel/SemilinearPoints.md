# Integral points of actual coefficient twists

This internal construction relates the actual integral sections and generic
evaluation of a coefficient-twisted model to the existing coefficient Galois
action. All rings and schemes have arbitrary common universe `u`.

For a group scheme over any base, pullback of sections along an epimorphism is
injective. Together with the existing surjectivity along a base isomorphism,
`twistIntegralSectionsEquiv` identifies the groups of actual integral sections
of a model and its twist when the integral coefficient map is an isomorphism.
No invertibility is needed for the generic evaluation identity
`twist_integralPointMap`: pulling back a section and evaluating it in the twist
equals pulling back its original generic evaluation. The proof projects
sections of the two pullback towers to the original group, uses the commuting
square and then cancels its comparison isomorphism.

For a field extension `L/k`, `rationalConjugate_eq_transport` identifies
canonical geometric semilinear transport with the published coefficient action
`rationalConjugate`. Its proof uses the actual pullback projection, the formula
for `baseChangeSectionHom_fst`, and the existing comparison between rational
points of a base change and points with extension-field coefficients. The
auxiliary `galoisDescentIso` names this same canonical isomorphism while exposing
the group-scheme base-change convention in its type.

Consequently, `twist_integralPointMap_galois` gives exactly the coefficient
conjugate of a section's original evaluation. If the coefficient action of a
specified automorphism preserves a model's integral-point image and the
integral base map is invertible, `galoisTwist_map_mem_integralPoints` proves that
the canonical generic isomorphism from its actual twist carries all integral
points into those of the model. Surjectivity of section pullback accounts for
every section of the twist.

For arbitrary models and a specified generic isomorphism,
`inv_map_mem_integralPoints_of_section_transport` proves the reverse inclusion
from an exact section transport, an inverse action on generic points, and
stability under that inverse action. It is an abstract range argument, using
injectivity and the inverse identity for maps on rational points induced by a
group-scheme isomorphism. `rationalConjugate_symm_apply` supplies the inverse
coefficient-action identity.

These are derived consequences of the published actual pullback constructions
and point correspondences and of the coefficient twist construction in
`SemilinearModel`. They do not assume or prove an extension criterion. This
unit constructs no integral semilinear isomorphisms, coherent descent datum, or
descended integral model, and is not a proof of KP Fact 2.10.16.
