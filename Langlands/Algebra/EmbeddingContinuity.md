# Continuous permutation of field embeddings

Worker 207.

This internal construction takes fields `k`, `K`, and `Ω`, with the two
`k`-algebra structures. The fields may have different universes.
`embeddingMulAction` is the action of `Aut_k(Ω)` on `K →ₐ[k] Ω`
obtained from `embeddingPermutationHom`: `σ` acts by `τ ↦ σ ∘ τ`.
`embedding_stabilizer_eq` identifies its stabilizer at `τ` with
`τ.fieldRange.fixingSubgroup`, as subgroups of `Aut_k(Ω)`.

When `K/k` is finite dimensional, `τ.equivFieldRange` identifies `K`
linearly with the image field of `τ`. That field is therefore finite
over `k`. Mathlib's `IntermediateField.fixingSubgroup_isOpen` shows
that its fixing subgroup is open in the Krull topology on `Aut_k(Ω)`.
This gives `embedding_stabilizer_isOpen`. The construction does not
assume that `Ω/k` is algebraic or that `K/k` is separable.

For any specified discrete topology on the embedding set,
`embeddingContinuousPermutation` is the continuous map
`Aut_k(Ω) × (K →ₐ[k] Ω) → (K →ₐ[k] Ω)` with this postcomposition
formula. Its continuity follows from the open stabilizers using
`continuousSMul_iff_stabilizer_isOpen`. The action is local to this
module's proofs; no global action or topology instance is installed
on algebra homomorphisms.

With an additional `Finite (K →ₐ[k] Ω)` instance,
`embeddingContinuousRepresentation` is the continuous map

`Aut_k(Ω) × ((K →ₐ[k] Ω) → ℤ) → ((K →ₐ[k] Ω) → ℤ)`

whose value at `(σ, m)` is `embeddingPermutationRepresentation σ m`,
or explicitly `τ ↦ m(σ⁻¹ ∘ τ)`. The integer function space has the
ordinary product topology of discrete integers. Since the index is
finite, this topology is discrete. For fixed `m`, each coordinate is
the composite of continuous inversion, a continuous embedding orbit,
and the function `m` from a discrete space. Coordinatewise continuity,
then discreteness of the function variable, gives joint continuity.
The underlying maps are exactly those of the existing permutation
representation, so its identity, composition, and additivity laws
remain in force.

These are intrinsic topological constructions from the existing
embedding permutation and Mathlib's Krull topology. They neither
construct a splitting of a Weil restriction nor identify a group
scheme lattice. Those comparisons are supplied by separate adapters.
