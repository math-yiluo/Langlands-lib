# Finite-separable Weil restriction in canonical embedding coordinates

Worker 207. This derived adapter applies the published finite-separable
tensor evaluation theorem to the existing Weil-restriction and actual
Galois lattice constructions.

Let `k`, `K`, and `Ω` be fields in one universe, with `k`-algebra
structures on `K` and `Ω`, finite-dimensional separable `K/k`, and
assume every `minpoly k x`, for `x : K`, splits after mapping into `Ω`.
The canonical tensor evaluation is then bijective by
`embeddingEvaluationStatement`; its proof is supplied by the imported
proof module, rather than assumed as a separate input.

`separableEmbeddingDecomposition` is the resulting actual algebra
isomorphism `Ω ⊗[k] K ≃ₐ[Ω] ((K →ₐ[k] Ω) → Ω)`. The canonical
splitting `separableEmbeddingIso` identifies the actual base change
of `WeilGm.groupScheme k K` with the split torus indexed by the
embeddings `K →ₐ[k] Ω`. `separableEmbeddingCommIso` gives the same
isomorphism in the commutative group-scheme category. The number of
coordinates is `finrank k K`, by `separableEmbedding_card`.

`separableEmbeddingCharacterEquiv` and
`separableEmbeddingCocharacterEquiv` identify the actual morphism
lattices with the integer functions on that finite embedding set.
Their Galois comparison lemmas state that the existing actual lattice
actions of each `σ : Aut_k(Ω)` are the permutation action
`m ↦ (τ ↦ m(σ⁻¹ ∘ τ))`. These constructions specialize the existing
embedding-coordinate comparisons, with their tensor bijectivity
hypothesis discharged by the finite-separable evaluation theorem.
The existing all-test coordinate formulas and perfect pairing remain
available through these same specialized equivalences.

`separableEmbeddingCharacterContinuousAction` and
`separableEmbeddingCocharacterContinuousAction` package these actual
actions as jointly continuous maps. The automorphism group has the
Krull topology, and each actual lattice has any specified discrete
topology. Their application lemmas identify the maps with the existing
actual Galois representations. These constructions specialize the
continuity adapters with the finite-separable evaluation proof; they
do not install global topology instances on scheme morphisms.

For a separably closed `Ω`, `separable_minpoly_splits` supplies the
splitting-polynomial hypothesis: the minimal polynomials in a separable
extension are separable and hence split in a separably closed field.
Consequently `isTorus_of_finite_separable` proves that the actual
Weil restriction is a torus, choosing `SeparableClosure k` as splitting
field and the canonical isomorphism above. It does not assume that
`K/k` is normal or that `k` is perfect. No smoothness or reductivity
descent theorem and no classification of arbitrary field tori is proved
in this adapter.

This is a specialization of the canonical evaluation and Weil-restriction
comparisons motivated by Milne, *Algebraic Groups* (2017), 2.61,
printed p.59 / PDF p.75. The exact citation and the underlying
finite-separable evaluation assertion are documented in
`SeparableTensorStatement.md`. The separable-closure specialization
uses Mathlib's `IsSepClosed.splits_codomain` and the existing definition
of `GroupScheme.IsTorus` as splitting over some field extension.

Source: registered `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The canonical equivariance and joint continuity packages are derived
from the existing actual-action adapters; they are not asserted to be
separate statements of Milne 2.61.
