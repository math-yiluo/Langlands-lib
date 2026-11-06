# The completion of a smooth representation

Author: Worker 6. Module `Langlands.Representation.Smooth.CompactCompletion`, namespace `Langlands.CompactCompletion`. Three definitions, `completion`, `translate` and `completionFixed`. Nothing is proved here except that the two subspaces are closed under the linear operations.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The relevant passages are:

- I.1.4 (printed p.9 / PDF p.15): the completion `M̄` of a nondegenerate module `M` over a ring with idempotents `A` is the projective limit `lim_{e ∈ Idem(A)} e·M` for the transition maps `f·M → e·M`, `m ↦ e·m` (`e ≤ f`). Equivalently, `M̄` is the set of families `{m̄(e)}_{e ∈ Idem(A)}` with `m̄(e) ∈ e·M` and `e·m̄(f) = m̄(e)` whenever `e ≤ f`. The order is that of I.1.1 (printed p.6 / PDF p.12): `e ≤ f` if `eAe ⊂ fAf`.
- I.1.4, Proposition (printed p.10 / PDF p.16): `M̄ ≅ Hom_A(A, M)`, which carries the left `A`-module structure `(a·φ)(b) = φ(ba)`.
- VI.9.7, proof (printed p.205 / PDF p.211): for a smooth representation `(π, V)` of `G` the source writes `V̄ = lim_K V^K`, the limit over compact open subgroups `K` of `G`. It uses that the idempotents `e_K` form a filtering system of idempotents of the Hecke algebra.

## Definitions

Let `G` be a topological group, `V` a complex vector space and `ρ : Representation ℂ G V` with `hρ : IsSmooth ρ`. Compact open subgroups are the published `Langlands.HarishChandraSchwartz.CompactOpenSubgroup G`, open subgroups whose underlying set is compact. For such a `K`, `e_K` is the published normalized average `Compact.averageMap ρ hρ K.1 K.2`, the projection of `V` onto `V^K`.

- `completion ρ hρ : Submodule ℂ (CompactOpenSubgroup G → V)` is the space of families `(v_K)` indexed by the compact open subgroups such that `e_K v_L = v_K` whenever `L ≤ K`. Taking `L = K` gives `e_K v_K = v_K`, so `v_K ∈ V^K`.
- `translate ρ g v` is the family `K ↦ ρ(g) v_{g⁻¹ K g}`, where `g⁻¹ K g` is the published `CompactOpenSubgroup.conj g⁻¹ K` (`CompactOpenSubgroup.conj g K` is `g K g⁻¹`).
- `completionFixed ρ hρ H : Submodule ℂ (completion ρ hρ)` is the subspace of families `v` with `translate ρ h v = v` for every `h ∈ H`, for a subgroup `H` of `G`.

## Comparison with the source

- **Indexing set.** The source indexes `V̄` by all idempotents of the Hecke algebra `H(G)`. The Lean definition indexes it by the idempotents `e_K` only, as the source does in the proof of VI.9.7. For `L ≤ K` one has `e_K H(G) e_K = H(G, K) ⊂ H(G, L) = e_L H(G) e_L`, so `e_K ≤ e_L` in the order of I.1.1. Thus the condition `e_K v_L = v_K` for `L ≤ K` is the source's compatibility condition `e·m̄(f) = m̄(e)` for `e = e_K ≤ f = e_L`. Every idempotent `e` of `H(G)` is bi-invariant under some compact open `K`, so `e ≤ e_K` for small `K`. Hence restricting a source family to the `e_K` is a bijection, with inverse `m̄(e) = e·v_K` for any `K` with `e ≤ e_K`. This comparison is the reason for the choice and is not proved in Lean. The Hecke algebra itself is not used.
- **The `G`-action.** For `v ∈ V` and `g ∈ G` one has `e_K π(g) v = π(g) e_{g⁻¹ K g} v`, since conjugation by `g` carries the normalized average over `g⁻¹ K g` to the one over `K`. So the action of `G` on `V̄` extending that on `V ⊂ V̄` (`v ↦ (e_K v)_K`) is given on components by `(g·v)_K = π(g) v_{g⁻¹Kg}`. This is the formula of `translate`. The Lean development does not prove that `translate` maps `completion ρ hρ` into itself; `completionFixed` only uses it to state the fixed-point condition. So `completionFixed ρ hρ H` is the source's `V̄^H`.
- **Relation to the general construction.** The Library's `Langlands.Algebra.NonUnitalModuleLeftLimit A M` is the limit of I.1.4 for a nonunital module `M` over a ring with idempotents `A`, indexed by all idempotents. Using it here would need the Hecke algebra of `G(F)` and the module structure of a smooth representation over it. The smooth-representation interface of the published Jacquet functors provides neither, so the completion is built directly from the averages `e_K`. No comparison between the two constructions is proved.
- **Topology.** The completion is defined as a vector space. The uniform structure of I.1.4 is not defined.
- **Scope.** The definitions do not assume `G` locally profinite. They are meant for groups of rational points of reductive groups over nonarchimedean local fields, where compact open subgroups form a basis of neighbourhoods of the identity. Without such a basis the definition still makes sense but need not be the source's completion.

## Provenance

These are **derived** concrete definitions of Renard's completion `V̄ = lim_K V^K` of I.1.4 and VI.9.7 and of its subspace of `H`-invariants. They use the published `Compact.averageMap` for `e_K`, the published `CompactOpenSubgroup` and `CompactOpenSubgroup.conj`, and no new axioms. The definitions are used by `Langlands.Representation.Exponents.LeviCompletionOppositeJacquetStatement` (Renard VI.9.7).
