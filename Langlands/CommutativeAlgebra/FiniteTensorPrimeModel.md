# Finite coefficient models of prime tensor ideals

For fields `K` and `L` with a `K`-algebra structure on `L`, and an arbitrary
commutative `K`-algebra `A`, the actual intermediate-field tensor map

`DVRAlgebraicBaseChange.stageMap K L A E : E ⊗[K] A →ₐ[K] L ⊗[K] A`

is faithfully flat for every intermediate field `E` of `L/K`.
`stageMap_faithfullyFlat` proves this assertion, and `stageMap_comap_map`
proves that every ideal `J` of `E ⊗[K] A` is the contraction of its extension
along this map. Neither result assumes that `L/K` is algebraic.

Given an algebraic extension `L/K`, a finite index type `ι`, and ideals
`I i` of `L ⊗[K] A` that are finitely generated and prime,
`FiniteTensorPrimeModel.construct I hfg hprime` constructs:

- one actual intermediate field `fieldStage`, finite dimensional over `K`;
- finitely generated prime ideals `ideal i` in `fieldStage ⊗[K] A`;
- equalities saying that extension of `ideal i` along the actual tensor map
  is exactly `I i`, and that `ideal i` is exactly the contraction of `I i`.

The structure extends `FiniteTensorIdealModel`, retaining its field,
finite-generation proofs, and extension equalities. The helper
`FiniteTensorIdealModel.ideal_eq_comap` identifies the ideals in every such
model with the contractions of their originals. The helper
`FiniteTensorIdealModel.isPrime` proves primality whenever the corresponding
original ideal is prime. The constructor adds these proved conclusions to
the previously constructed finite ideal model; it assumes no model-existence
hypothesis. The field types, algebra type, and index type have four
independent universes. No finite-type, Noetherian, reducedness, or domain
hypothesis on `A` is imposed.

## Implemented proof

Commuting the tensor factors over `E` and canceling base change gives an
`E`-algebra equivalence

`(E ⊗[K] A) ⊗[E] L ≃ₐ[E] L ⊗[K] A`.

Tensor induction proves that this equivalence sends `x ⊗ 1` to
`stageMap K L A E x`. This coefficient identity upgrades the equivalence
to one over `E ⊗[K] A`, with the target action induced by the actual stage
map. The nonzero vector space `L` over the field `E` is faithfully flat.
Mathlib's base-change instance gives faithful flatness of
`(E ⊗[K] A) ⊗[E] L` over `E ⊗[K] A`; transport along the linear equivalence
gives the claimed faithful flatness of the stage map.

`Ideal.comap_map_eq_self_of_faithfullyFlat` supplies the contraction equality.
Substituting the ideal model's extension equality gives `ideal_eq_comap`.
Contraction of a prime ideal is prime, proving `isPrime`. Finally the
constructor applies these two helpers to `FiniteTensorIdealModel.construct`.
This proof preserves the independent universes by using module faithful
flatness and explicit equivalences.

## Provenance and scope

This is a derived algebraic strengthening of the finite-coefficient step in
Stacks Project, Lemma 33.8.15 (tag 04KZ), first paragraph of the proof.
Registered source: `stacks-finite-coefficient-descent-04KZ-2026-11-04`,
retained HTML SHA-256
`9f5bd264065a4948acc0c96e0c72e7431d4d6c288a925989c05802ee76c3a15b`.
The source takes finitely many generators of a geometric-component prime
ideal and chooses a finite coefficient extension containing them. The
imported finite ideal model implements this coefficient step. The present
unit additionally proves that its defining ideals are the prime
contractions, using faithfully flat scalar extension. The finite-family,
arbitrary-algebra form is an internal generalization of that algebraic step.

This unit does not establish descent of scheme components, continuity of
the Galois action on components, finite separable component splitting, the
full 04KZ lemma, or Conrad's geometric-fibre theorems. In particular it
makes no claim that a general algebraic extension is separable. Those
scheme-level and consumer obligations remain separate.
