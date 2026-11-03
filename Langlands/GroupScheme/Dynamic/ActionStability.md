# Stability of Dynamic functors under a commutative acting group

This internal helper derives all-test stability directly from the published
definitions of automorphic actions and Dynamic subgroup functors. It supports
the application of the uniqueness assertion in Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition, Proposition 3.3.6 (printed
pp. 109–110, PDF pp. 135–136), to the Dynamic functors described in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Propositions 2.11.1–3
(printed pp. 130–132, PDF pp. 161–163). The 2024 corrections, PDF p. 25,
alter the notation in this section without changing these conclusions.

Let a commutative group scheme act by automorphisms on any group scheme over
any base, and restrict its action along a homomorphism from the multiplicative
group. The whole group preserves the restricted parabolic, centralizer and
identity-limit subgroup functors. No smoothness, representability, torus,
connectedness or genericity hypothesis is used.

The proof acts on an affine-line orbit extension by the acting point pulled
back from the test scheme, using the actual morphism `actOnAffineLine`.
Commutativity of the acting group identifies the
restriction of this family with the orbit of the acted-on point. Naturality
of the action shows that its zero value is the action on the original zero
value, using the imported `AutomorphicAction.evalZero_act` from
`Rational/RootSubgroupStability`. Thus existence of an extension, and existence of one with identity
zero value, are both preserved. Centralizer stability uses the already proved
all-refinement fixed-point stability theorem. The last three lemmas specialize
this argument to conjugation along a homomorphism from the commutative group.
Every assertion concerns morphisms on all test schemes, including nonreduced
ones.
