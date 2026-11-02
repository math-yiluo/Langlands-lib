# Continuous Galois actions on the actual Weil-restriction lattices

Worker 207.

Take fields `k`, `K`, and `Ω` in the same universe, with `k`-algebra
structures on `K` and `Ω`, finite-dimensional `K/k`, a finite
homomorphism index `K →ₐ[k] Ω`, and an explicit bijectivity proof
`h` for `embeddingEvaluation k K Ω`. Finite projectivity of `K`
over `k`, required for the Weil restriction, follows from these
field and finite-dimensional hypotheses. Write `W_Ω` for the actual
base change to `Spec Ω` of `WeilGm.commGroupScheme k K`.

For any specified discrete topology on `characterLattice W_Ω`,
`embeddingCharacterContinuousAction` is the continuous map

`Aut_k(Ω) × characterLattice W_Ω → characterLattice W_Ω`

whose underlying value at `(σ, χ)` is exactly the actual
`characterLattice.galoisRepresentation k Ω (WeilGm.commGroupScheme k K) σ χ`.
The automorphism group carries Mathlib's Krull topology.
`embeddingCharacterContinuousAction_apply` records this equality.
The identity and multiplication laws are those of this existing
representation.

Likewise `embeddingCocharacterContinuousAction`, for any discrete
topology on `cocharacterLattice W_Ω`, is the continuous joint action
given by the actual `cocharacterLattice.galoisRepresentation`.
Its application lemma identifies that same underlying action.

The construction uses `embeddingCharacterEquiv` and
`embeddingCocharacterEquiv`. Both equivalences and their inverses
are continuous because the lattices and the finite integer function
space are discrete. Their previously established equivariance
identifies the actual Galois action with the continuous map
`embeddingContinuousRepresentation`, namely
`(σ, m) ↦ (τ ↦ m(σ⁻¹ ∘ τ))`. Composing the coordinate equivalence,
this continuous action, and the inverse equivalence gives continuity
on the actual lattice. The implemented proof then uses equivariance
to identify that composite with the original representation.

This is an intrinsic topological adapter for the actual scheme
morphism lattices, using their existing algebraic Galois comparison.
It does not assume `Ω/k` algebraic or `K/k` separable; the supplied
bijectivity proof is retained. In particular it does not derive that
proof from finite separability or give a classification of field tori.
No topology instance on group scheme morphisms is installed globally.
