# Commutativity of the Hecke algebra of an open normal subgroup

Author: Worker 1789.

This is a supporting module for the proof of Renard's VI.4.3 Corollary (ii)
(`RationalSummandEndCommutativeProof`). It extends the generic development of
`NormalSubgroupHecke`, `NormalSubgroupHeckeDomain` and `NormalSubgroupHeckeSeparation`, in
namespace `Langlands.CuspidalSupport.NormalHecke`. Here G is a topological group, H an open
normal subgroup, ρ an irreducible smooth complex representation of H, I = `inducedRep H ρ`
the compact induction ind_H^G ρ, and R = `End I` its endomorphism ring. π is a complex
representation of G on an arbitrary vector space; it need not be smooth. Source: David
Renard, *Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.3, Corollary (ii) and its
proof, printed p.155 / PDF p.161. The declarations here are internal helpers. Their route
is not Renard's; the section "Relation to the source" compares the two.

## Linear algebra and characters

- `isIrreducible_comp`: if σ is an irreducible representation of K' and c : K →* K' is
  surjective, then σ ∘ c is irreducible. The two representations have the same invariant
  subspaces, which gives an order isomorphism of their subrepresentation lattices.
- `eq_zero_of_forall_character` (Dedekind's independence of characters, with vector
  coefficients): let Q be a group whose characters Q →* ℂˣ separate points, e : ι → Q
  injective and t : ι → V finitely supported. If ∑ᶠ i, ω(e i) • t i = 0 for every character
  ω, then t = 0. The evaluations ω ↦ ω(e i) are distinct monoid homomorphisms
  (Q →* ℂˣ) →* ℂ, hence linearly independent (Mathlib's `linearIndependent_monoidHom`).
  For each linear form l on V, linear independence gives l(t i) = 0. Then t i = 0 by
  `Module.forall_dual_apply_eq_zero_iff`.
- `twist ω π` is the representation g ↦ ω(g) π(g) for a character ω : G →* ℂˣ.
  `twistRes ω hω π σ` is the linear equivalence Hom_H(σ, Res_H (twist ω π)) ≃
  Hom_H(σ, Res_H π) for ω trivial on H. It keeps the underlying linear map.
- `rank_le_one_iff_of_equiv`: linearly equivalent spaces, in possibly different
  universes, have dimension at most one simultaneously.
- `homLinearEquiv A B`: morphisms A ⟶ B of smooth representations are linearly
  equivalent to equivariant linear maps (`SmoothRep.hom` and `SmoothRep.ofHom`).

## Frobenius reciprocity and the right module

- `frobenius H ρ hH τ`: the linear equivalence Hom_G(I, τ) ≃ Hom_H(ρ, Res_H τ) for a
  representation τ of G. It sends T to T ∘ (w ↦ f_w), where f_w is the published unit
  function. The inverse is the published coset sum f ↦ ∑_{Hx} τ(x⁻¹) φ(f(x)). The two
  identities are the published `cosetSum_resIntertwining_comp`, `cosetSum_unitMap` and
  `cosetSum_comp_unitMap` of `OpenAdjunction`.
- `rightAction` and `rightModule`: precomposition T ↦ T ∘ β makes Hom_G(I, τ) a module
  over Rᵐᵒᵖ, that is, a right R-module. `rightModule_isScalarTower` makes it compatible
  with the complex scalars. The instance is local to this module.

## Semisimplicity of Res_H I and lifting

- `conjHom H x` is conjugation h ↦ x h x⁻¹ of H, which is surjective
  (`conjHom_surjective`).
- `translateMap H ρ hH x`: the map w ↦ x⁻¹ · f_w, from the conjugate ρ ∘ conjHom x to
  Res_H I. Equivariance (`translate_unitFunction`) follows from equivariance of the unit
  map. It is injective (`translateMap_injective`), because the value of x⁻¹ · f_w at x
  is w (`eval_translateMap_self`).
- `isSemisimpleModule_res`: Res_H I is a semisimple ℂ[H]-module. The images of the maps
  `translateMap x` are simple submodules, because ρ ∘ conjHom x is irreducible
  (`isIrreducible_comp`). They span Res_H I: by `cosetSum_unitMap`, every f ∈ I is the
  finite sum over the cosets Hx of x⁻¹ · f_{f(x)}, the term at Hx being in the image of
  `translateMap x`. Mathlib's `isSemisimpleModule_of_isSemisimpleModule_submodule'`
  concludes.
- `exists_lift`: if T : I → π is surjective and G-equivariant, then every H-map S from an
  H-representation σ to Res_H π lifts to an H-map ψ : σ → Res_H I with T ∘ ψ = S. This is
  Mathlib's `IsSemisimpleModule.lifting_property`, read through the identification of
  intertwining maps with ℂ[H]-linear maps (`equivLinearMapAsModule`).
- `surjective_of_ne_zero`: a nonzero equivariant map into an irreducible representation
  is surjective (Mathlib).
- `exists_end_comp_eq`: if T : I → π is surjective, every T' : I → π equals T ∘ β for
  some β ∈ R. Lift the H-map T' ∘ (w ↦ f_w) through T to ψ : ρ → Res_H I, and take
  β = the coset sum of ψ. Then T ∘ β and T' agree on all f_w by `cosetSum_comp_unitMap`,
  so they are equal by Frobenius reciprocity.

## Commutativity implies multiplicity at most one

- `rank_le_one_of_commute'`: assume `[Countable (G ⧸ H)]`, `Module.rank ℂ ρ ≤ ℵ₀`, π
  irreducible, j : ρ → Res_H π nonzero and R commutative. Then Hom_H(ρ, Res_H π) has
  dimension at most one. By Frobenius reciprocity it suffices to treat M = Hom_G(I, π).
  The coset sum T₀ of j is nonzero. Every nonzero T ∈ M is surjective, so by
  `exists_end_comp_eq` every element of M is T ∘ β. Hence M is a simple right R-module
  (`isSimpleModule_iff_toSpanSingleton_surjective`). R has countable dimension
  (`rank_end_le` of `NormalSubgroupHeckeSeparation`). So the published Schur–Dixmier lemma
  `Langlands.Renard.schurScalarOfAlgebraRankCountable` (Renard B.II), applied to Rᵐᵒᵖ and
  M, makes every Rᵐᵒᵖ-linear endomorphism of M a scalar. Since R is commutative, the
  action of each a ∈ Rᵐᵒᵖ is itself Rᵐᵒᵖ-linear, hence equal to some scalar c. Every
  T ∈ M has the form a • T₀ = c • T₀, so M has dimension at most one (`rank_le_one_iff`).
- `rank_le_one_of_ne_zero`: assume π irreducible, j : ρ → Res_H π nonzero and
  dim Hom_H(ρ, Res_H π) ≤ 1. Then dim Hom_H(σ, Res_H π) ≤ 1 for every irreducible
  representation σ of H, with carrier in any universe. If there is no nonzero S : σ →
  Res_H π, the space is zero. Otherwise, the coset sum T of j is surjective, and
  `exists_lift` lifts S to ψ : σ → Res_H I, which is nonzero. Choose v and x with
  ψ(v)(x) ≠ 0. Then ε = (u ↦ ψ(u)(x)) is a nonzero H-map σ → ρ ∘ conjHom x, since
  ψ(u)(x h) = ρ(x h x⁻¹) ψ(u)(x). Both sides are irreducible, so ε is bijective (Mathlib's
  `bijective_or_eq_zero`). The map S' ↦ π(x) ∘ S' ∘ ε⁻¹ is an injective linear map
  Hom_H(σ, Res_H π) → Hom_H(ρ, Res_H π). Equivariance uses
  π(x) π(x⁻¹ m x) = π(m) π(x) for m ∈ H. `LinearMap.lift_rank_le_of_injective` gives the
  bound.
- `rank_le_one_of_commute` combines the two results: under the hypotheses of the first
  one, dim Hom_H(σ, Res_H π) ≤ 1 for every irreducible σ.

## Multiplicity at most one implies commutativity

- `cosetTerm_twist`: for ω trivial on H, the coset-sum term of the twisted map at Hx is
  ω(x)⁻¹ times the untwisted term π(x⁻¹) j(f(x)).
- `comp_mk'_eq_one`: a character of G ⧸ H, pulled back to G, is trivial on H.
- `commute_of_rank_le_one`: assume that the characters of G ⧸ H separate points, that
  j : ρ → Res_H π is injective, and that dim Hom_H(ρ, Res_H π) ≤ 1. Then R is
  commutative. Irreducibility or smoothness of π is not needed. Let γ = αβ − βα. For a
  character ω₀ of G ⧸ H, with pullback ω to G, the space Hom_G(I, twist ω π) is linearly
  equivalent to Hom_H(ρ, Res_H π) (`frobenius`, `twistRes`). So it has dimension at most
  one and contains the nonzero coset sum J of j. Therefore J ∘ δ = c_δ J for every δ ∈ R,
  and J ∘ γ = c_α c_β J − c_β c_α J = 0. Fix w ∈ ρ and F = γ(f_w). Applying J ∘ γ = 0 at
  f_w for the character ω₀⁻¹ gives ∑ᶠ_{Hx} ω₀(xH) • π(x⁻¹) j(F(x)) = 0, by
  `cosetTerm_twist`. The cosets Hx are indexed injectively by G ⧸ H through
  `leftQuotientEquiv`. Dedekind's lemma `eq_zero_of_forall_character` then gives
  π(x⁻¹) j(F(x)) = 0 for every x. So F(x) = 0 by injectivity of j, and F = 0. Since
  γ(f_w) = 0 for every w, γ = 0 by the published `end_ext`.

## Relation to the source

Renard proves Corollary (ii) through the equivalence of categories M(G)[π] ≃ mod-A of
VI.4.1, which needs π supercuspidal. By that equivalence, the simple right A-modules are
the spaces Hom_{⁰G}(ρ, Res(π ⊗ ω)) for unramified characters ω, all of dimension the
multiplicity m of ρ in Res π. If m = 1, the Lemma of VI.4.3 embeds A in a product of
copies of ℂ. Conversely, if A is commutative, every simple right A-module has dimension 1.

The Lean proof uses neither VI.4.1 nor the Lemma, and no cuspidality.

- Forward direction: it uses the single right module Hom_G(I, π) ≅ Hom_H(ρ, Res π). It
  proves simplicity directly from semisimplicity of Res_H I, and dimension one from the
  Schur–Dixmier lemma of B.II with commutativity. A Clifford-type step then passes from ρ
  to an arbitrary irreducible σ.
- Converse: it keeps Renard's family of right modules Hom_G(I, π ⊗ ω), each of dimension
  at most one because Res_H(π ⊗ ω) = Res_H π. In place of the Lemma, it uses Dedekind's
  independence of the characters ω of G ⧸ H to show that an element of R acting by zero
  on all of them is zero.
