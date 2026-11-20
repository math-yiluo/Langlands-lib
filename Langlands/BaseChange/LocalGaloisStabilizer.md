# Trivial Galois stabilizer for a local representation

`HasTrivialGaloisStabilizer F ρ` says that for every nonidentity element `τ` of the group of `F`-automorphisms of `E`, the representation `ρ` of `GL_n(E)` and the action `g ↦ ρ(τ(g))` are inequivalent. The group map applies `τ` entrywise. The defining clause uses the existing `entrywiseAut` convention from the σ-lift construction.

This predicate packages the condition on the local isomorphism class used with Henniart–Herb (1995), Proposition 5.5, and in Harris (1998), Proposition 4.8. Requiring inequivalence for every nonidentity element gives the same condition with inverse pullback, since inversion permutes the nonidentity elements.
