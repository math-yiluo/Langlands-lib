# Proof of descent of isomorphisms between trivial modules

The entry theorem `Langlands.Scheme.Modules.trivialIsoDescent` proves the exact
`TrivialIsoDescentStatement`. Its helper
`compatibleIsoDescent_of_trivializations` works for every effective epimorphism.

`baseTrivialization_compatible` obtains compatibility of pulled-back base
trivializations from the canonical comparison's action on `pullbackUnitIso`
and naturality. `scalar_compatible_of_base_trivializations` conjugates the
compatible isomorphism by those trivializations. Cancelling the isomorphisms
and using compatibility shows that the resulting structure-module scalar has
equal pullbacks along every equal-composite pair.

Compatible-global-unit descent gives a unit `t` on the base. The scalar
injectivity theorem identifies the pullback of `structureAutOfUnit t` with the
normalized isomorphism. Transport through the base trivializations therefore
gives an isomorphism whose actual `mapIso` pullback equals the prescribed one.

For uniqueness, `units_pullback_injective` represents two base units by maps to
the existing multiplicative-group scheme. Naturality and epimorphism
cancellation show that equal pulled-back units are equal. The helper
`normalizeIso_pullback` shows that normalizing a base isomorphism commutes with
pullback. Scalar injectivity, unit injectivity, and cancellation of the base
trivializations then prove `pullbackIso_injective_of_trivializations`, which
establishes uniqueness of the constructed lift.

The entry theorem installs the effective-epimorphism instance supplied by
Mathlib for a quasi-compact flat surjection. This is an internal deduction from
the published scalar and canonical-pullback APIs. It proves descent only for
isomorphisms between modules with global base trivializations; arbitrary
line-bundle gluing and object effectivity remain separate.
