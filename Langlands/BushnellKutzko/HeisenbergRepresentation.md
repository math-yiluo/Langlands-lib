# Heisenberg representations of a simple character

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Proposition (5.1.1), printed p. 158 (PDF p. 170). This is definition 2 of Task 7427.

## Setting

`F` is a field with a valuative relation (in applications a nonarchimedean local field) and `V` an `F`-vector space; `G = (Module.End F V)ˣ = Aut_F(V)`. The hereditary order `𝔄` is given by an `𝔬_F`-lattice chain `L` (Task 7398). The groups `H^m(β, 𝔄) = simpleHGroup L n β tail m` and `J^m(β, 𝔄) = simpleJGroup L n β tail m` are those of Task 7422, definition 2, relative to the tail `tail` of a defining sequence starting at `β`. In the statements of Task 7427 these arguments come from a simple stratum `S = [𝔄, n, 0, β]` and a defining-sequence choice `q`, as `S.chain S.n S.b q.tail`. Simple characters `θ ∈ C(𝔄, 0, β)` are characters `H^1(β, 𝔄) →* ℂˣ` (`simpleCharacters … 0`).

Representations are Mathlib's `Representation ℂ K W`.

## Definitions and lemmas

- `simpleHCutoff_ge_simpleJCutoff`, `simpleHLattice_le_simpleJLattice` and `simpleHGroup_le_simpleJGroup` prove `ℌ(β, 𝔄) ⊆ 𝔍(β, 𝔄)` and `H^m(β, 𝔄) ⊆ J^m(β, 𝔄)` for the Task 7422 definitions, by induction on the tail of the defining sequence (the `H` cutoff `⌊r/2⌋ + 1` is at least the `J` cutoff `⌊(r+1)/2⌋`). The inclusion `H^1 ≤ J^1` is used to restrict `η` to `H^1`.
- `IsSmoothRepresentation ρ`, for a representation `ρ` of a subgroup `K ≤ G`: there are an `𝔬_F`-lattice chain `L` and `m` such that `ρ(k) = 1` for every `k ∈ K ∩ U^m(L)`. The groups `U^m(𝔄)` for the orders `𝔄` of lattice chains (Task 7398, `LatticeChain.unitFiltration`) form a neighbourhood basis of `1` in `G` (a standard fact, not proved here) when `F` is a nonarchimedean local field and `V ≠ 0` is finite-dimensional, so this is the lattice form of "the kernel of `ρ` is open in `K`". The topology itself is not used.
- `IsHeisenbergRepresentation L n β tail θ η`, for a character `θ` of `H^1(β, 𝔄)` and a representation `η : Representation ℂ J^1(β, 𝔄) W`: the representation `η` *lies over* `θ`. It says that `W` is finite-dimensional, `η` is smooth (`IsSmoothRepresentation`) and irreducible (Mathlib's `Representation.IsIrreducible`), and there is a nonzero `H^1(β, 𝔄)`-homomorphism from the one-dimensional representation `characterRepresentation θ` to the restriction of `η` to `H^1(β, 𝔄)`, that is, the restriction contains `θ`.

The definition is a predicate, not a choice of `η`. BK93 (5.1.1) asserts that such an `η` exists and is unique up to isomorphism, that its restriction to `H^1` is a multiple of `θ`, that `(dim η)^2 = (J^1 : H^1)`, and that its intertwining is `J^1 B_β^× J^1`. These are statement V1 of Task 7427, not part of this definition.

The definition makes no case distinction. It applies unchanged when `E = F` (`β` scalar), where BK93 has `H^1 = J^1 = U^1(𝔄)`.
