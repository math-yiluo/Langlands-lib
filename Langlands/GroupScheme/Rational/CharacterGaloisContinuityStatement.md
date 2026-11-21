# Continuity of Galois transport on rational characters

`Langlands.GroupScheme.CharacterGaloisContinuityStatement.{u}` is the
proposition that the natural action on the characters of a group scheme
after an algebraic field extension is continuous for the discrete
topology on the character module.

The fields `k K : Type u` have `Algebra k K` and
`Algebra.IsAlgebraic k K`. Thus the extension may be infinite, inseparable
or nonnormal. The structure morphism of the actual group scheme `G` over
`Spec k` is quasi-compact and quasi-separated. This includes all affine
group schemes and permits arbitrary group laws.

The representation `rationalCharacters.galoisRepresentation k K G`
uses actual homomorphisms \(G_K \to \mathbb G_{m,K}\) and the transport
induced by the field automorphisms in `K ≃ₐ[k] K`. Mathlib equips this
automorphism group with the Krull topology. `Langlands.IsSmooth` asks
that each character be fixed by some open subgroup. This is the
open-stabilizer criterion for a continuous action on a discrete set.

Milne, *Algebraic Groups* (2017), §12.g, printed p. 239 (PDF p. 255),
states continuity of the action on the characters over the separable
closure and gives the open-subgroup formulation. That passage treats
algebraic groups under the finite-type convention of Definition 1.1
and its preamble, printed p. 6 (PDF p. 22), and the affine convention
in the Chapter 12 opening, printed p. 230 (PDF p. 246). Taking
`K = SeparableClosure k` on that class gives the continuity assertion
in the source. The present target extends it using finite fields of
definition for morphisms from a quasi-compact, quasi-separated source
to the locally finitely presented multiplicative group. The registered
source `milne-2017-algebraic-groups` has SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
