# Smooth representations as nondegenerate Hecke modules: construction

Author: Worker 6. Module `Langlands.Representation.Hecke.NondegenerateModuleFunctor`, namespace `Langlands.Hecke`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, III.1.3 (the action `π(T)` of `H(G)` on a smooth representation) and III.1.4 (the functor from `M(G)` to `M(H(G))` in the Theorem and its proof), printed pp.59–60 / PDF pp.65–66, with the definitions of nondegenerate modules of I.1. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This is a definition unit. It constructs one functor and proves the facts its construction needs. It does not assert that the functor is an equivalence.

## The source

Renard identifies `𝒟(G)` with `H(G)` through a Haar measure `μ_G`. A smooth representation `(π, V)` becomes a module over `H(G)` through `π(f) = ∫_G f(g) π(g) dμ_G(g)` (III.1.3, Remark). The Theorem of III.1.4 begins: if `(π, V)` is smooth, the `H(G)`-module `V` is nondegenerate, because a vector fixed by a compact open `K` satisfies `π(e_K) v = v`. Every morphism of `M(G)` is a morphism of `M(H(G))`. These two observations define a functor `M(G) → M(H(G))`. The Theorem asserts that it is an equivalence.

## Setting

- `G : Type u` is a group with a topology, `[NonarchimedeanGroup G]` and `[LocallyCompactSpace G]`, with measurable structure `[BorelSpace G]`. With these instances, compact open subgroups form a basis of neighbourhoods of the identity (the published `Langlands.compactOpenSubgroupBasis`). Renard explicitly allows this condition as the definition of t.d. groups (II.1.1); by van Dantzig's theorem it is equivalent to local compactness and total disconnectedness. No Hausdorff hypothesis is needed for the construction.
- `μ` is a left Haar measure (`μ.IsHaarMeasure`).
- `HeckeAlgebra μ` is the published Haar Hecke algebra: compactly supported locally constant functions with convolution `(f * g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)`, a nonunital ring (module `Hecke/Convolution`).
- `Algebra.NonUnitalModule`, `Algebra.IsNondegenerate` and `Algebra.NondegenerateModuleCat` are the published Chapter I notions (module `Algebra/NonUnitalModule`). A nondegenerate module is one in which every vector is fixed by an idempotent of the ring, Renard's `M(A)` for an idempotented ring `A`.

## Declarations

- `heckeNonUnitalModule μ ρ hρ`: for a smooth `ρ : Representation ℂ G V`, the module structure of `HeckeAlgebra μ` on `V` given by the published nonunital algebra homomorphism `heckeAction μ ρ hρ : HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ V`, via the published `Algebra.NonUnitalModule.ofLinearEndHom`. So `f • v = heckeAction μ ρ hρ f v = ∫ f(g) ρ(g) v dμ(g)`.
- `heckeNonUnitalModule_isNondegenerate`: this module is nondegenerate. For `v` fixed by an open subgroup `U`, choose a compact open `K ⊆ U`. The normalized indicator `e_K = μ(K)⁻¹ 1_K` is an idempotent (published `normalizedIndicator_idempotent`) with `e_K • v = v` (published `heckeAction_normalizedIndicator_of_fixed`).
- `heckeNondegenerateModule μ A`: for `A : SmoothRep.{0, u, v} ℂ G`, its carrier with this module structure, as an object of `NondegenerateModuleCat.{u, v} (HeckeAlgebra μ)`.
- `heckeNondegenerateModuleMap μ f`: for a morphism `f : A ⟶ B`, the same additive map, which commutes with the Hecke action by the published `integratedAction_intertwiner`.
- `heckeNondegenerateModuleFunctor μ : SmoothRep.{0, u, v} ℂ G ⥤ NondegenerateModuleCat.{u, v} (HeckeAlgebra μ)`, with these object and morphism maps. The identity and composition laws hold by definition.

## Remarks

- The modules are modules over the ring `HeckeAlgebra μ`, as in Chapter I, and their morphisms are additive maps compatible with the action. The complex structure of `V` is not part of the target. For a nondegenerate module over the `ℂ`-algebra `H(G)` it is recovered through the action of `c e_K`.
- That the functor is an equivalence (III.1.4, Theorem) is a separate statement unit.
