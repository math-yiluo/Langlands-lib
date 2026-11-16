# Supplied schemes representing group-scheme isomorphisms

Worker 217.

This internal interface packages an actual scheme over an arbitrary base
representing natural local group isomorphisms on every test. Its existence
is not assumed proved. The purpose is to derive the action required by the
integral inner-isomorphism torsor from an actual universal isomorphism.

`GroupIsomorphismScheme G H` consists of a parameter scheme over the base, a
`LocalGroupIso G H parameter`, and bijectivity, for every relative test `T`,
of refinement of that universal family along `T ⟶ parameter`.
`LocalGroupIso` includes a group isomorphism on every further test and
naturality under every refinement. Thus this interface concerns actual
scheme-valued tests and preserves their full group structures.

`pointsEquiv` and `classify` implement that bijection, and `comp_classify`
proves naturality in `T`. `hom_ext` uses all-refinement equality of evaluated
isomorphisms to detect equality of parameter points.
`baseChangeIsoEquiv` combines this interface with the published equivalence
between natural local isomorphisms and actual isomorphisms of the two
base-changed group schemes.

Given any supplied `AutomorphicAction A G`, `actionHom` classifies the
universal family that sends `(d, phi)` to `phi` precomposed with the
automorphism given by `d` inverse. `actionHom_eval` proves this equation
on every test. `modObj` proves the unit and multiplication laws from the
same evaluation equation, the uniqueness in the representation property,
and the laws of the supplied automorphic action. It is an actual categorical
left action, with `smul_eval` giving its exact evaluation equation.

These are internal constructions from the imported Library interfaces,
not assertions of relative isomorphism representability or of a quotient
by inner automorphisms. No flatness, surjectivity, finiteness, torsor
condition or existence theorem is asserted by this module.
