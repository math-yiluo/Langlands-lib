# Stabilizers of lines in `Hom(ρ, Res π)` through `End(ind_H^G ρ)`

Author: Worker 33. Module
`Langlands.Representation.CuspidalSupport.NormalHeckeLineStabilizer`, namespace
`Langlands.CuspidalSupport.NormalHecke`. It imports the published `NormalHeckeCenter` and
the new `Langlands.Algebra.RankOneGradedLagrangian`.

This module proves Renard's Lemma of VI.4.4 for a general open normal subgroup with a
degree map (`lineStabilizer`). The module `RationalSummandStabilizerLemmaProof` then
specializes it to `⁰G`. The route is not Renard's (see the last section).

## Setting

`G` is a topological group. `H` is a subgroup with `hH : IsOpen H`, normal where stated, and
`ρ : SmoothRep ℂ H` is irreducible where stated. `p : G → ι` satisfies `hp : IsDegree H p`:
it is additive into an additive commutative group `ι`, with kernel `H`. The published
`NormalHecke` development (modules `NormalSubgroupHecke`, `NormalHeckeGrading`,
`NormalHeckeModule`, `NormalHeckeTwist`, `NormalHeckeCenter`) supplies:

- `I = inducedRep H ρ = ind_H^G ρ`, and for `α ∈ End I` its value `endValue H ρ hH α g`, an
  endomorphism of `ρ`, written `φ_α(g)` below;
- `component H ρ hH p a`: the endomorphisms supported in degree `a`. With `gradedAlgebra`
  these grade `End I`. `isRankOneGrading` (which needs `hrank : rank ρ ≤ ℵ₀`) says each
  piece has rank at most one and nonzero homogeneous elements are invertible;
- `e = inducedLiftHomEquiv H ρ hH π : Hom(I, π) ≃ Hom_H(ρ, π|_H)` (Frobenius reciprocity,
  with `π` lifted to the universe of `I`);
- `homAction`: the anti-multiplicative action `α ↦ (φ ↦ α ≫ φ)` of `End I` on `Hom(I, π)`;
  `surjective_homAction` (Burnside) and `mem_radical_iff` (twist detection).

For `j : ρ → π|_H` with image `W`, the predicates of the target statement are `InH j g`
(`π(g) W = W`), `InN g` (`ρ^g ≅ ρ`) and `InHtilde j g` (`ρ_H^g ≅ ρ_H`, read through `j`).

## Values and Frobenius reciprocity

- `endValue_ne_zero_of_mem_component`: a nonzero `α` of degree `p g` has `φ_α(g) ≠ 0`.
- `exists_mem_component_endValue_eq`: given `A : End ρ` intertwining `ρ^g` with `ρ`
  (`A ρ(y) = ρ(x) A` whenever `y = g⁻¹ x g`), there is `α` of degree `p g` with
  `φ_α(g) = A`. It is built with the published `endOfHecke` and `inverseFunction_mem`.
- `hom_inducedLiftHomEquiv_comp`: for `α` of degree `p g` and `φ : I → π`,
  `e(α ≫ φ)(w) = π(g⁻¹)(e φ (φ_α(g) w))`. This is the published
  `hom_inducedLiftHomEquiv_apply` together with `hom_of_support`.
- `hom_comp_symm_apply` is the same formula with `φ = e⁻¹ j`.
- Small lemmas: `smul_hom_apply`, `restrict_hom_ext`, `hom_restrict_apply`,
  `zero_hom_apply`, `rep_mul_apply`, `eq_zero_of_rep_apply_eq_zero`, `rep_apply_congr`,
  `eq_rep_apply_of_rep_apply_eq`, and `injective_of_ne_zero` (a nonzero map out of the
  irreducible `ρ` is injective).
- `exists_mem_component_comp_eq_self`: let `j` be injective and suppose `π(k)` maps `W` into
  `W`. Define `R : End ρ` by `j(R w) = π(k) j(w)`. Then `R` intertwines `ρ^k` with `ρ`, and
  the `α` of degree `p k` with `φ_α(k) = R` satisfies `α ≠ 0` and
  `α ≫ e⁻¹ j = e⁻¹ j`.

## The three subgroups

- `inH_of_mem`: elements of `H` stabilize `W`.
- **`inN_iff`**: `InN g` holds iff the piece of degree `p g` is nonzero. Forward: use
  `exists_mem_component_endValue_eq`. Backward: `φ_α(g)` is bijective
  (`bijective_endValue`) and intertwines (`endValue_conj`).
- **`inH_iff`** (injective `j`): `InH j g` holds iff the piece of degree `p g` is nonzero and
  each of its elements `u` satisfies `u ≫ e⁻¹ j = c • e⁻¹ j` for some `c`. Forward: use
  `exists_mem_component_comp_eq_self` and the rank-one property. Backward: by
  `hom_comp_symm_apply`, `j(φ_α(g) w) = c • π(g) j(w)` with `c ≠ 0`, and `φ_α(g)` is
  bijective. So `π(g) W = W`.
- `inN_of_inHtilde`: an `A` witnessing `ρ_H^g ≅ ρ_H` also witnesses `ρ^g ≅ ρ`. Apply its
  defining property to `k ∈ H`.
- **`mul_comm_of_inHtilde`**: if `InHtilde j g` holds through `A` and `InH j k` holds, then
  every element of the piece of degree `p g` commutes in `End I` with every element of the
  piece of degree `p k`.
  Proof. Take `α` of degree `p g` with `φ_α(g) = A`, and `β` of degree `p k` fixing `e⁻¹ j`
  (`exists_mem_component_comp_eq_self`). `InH j (g k g⁻¹)` holds by `inH_iff`, since
  `p(g k g⁻¹) = p k`. The defining property of `A` then gives
  `β ≫ (α ≫ e⁻¹ j) = α ≫ e⁻¹ j`. Write `α β = c • β α` (rank one). Composing with `e⁻¹ j`
  gives `c • (α ≫ e⁻¹ j) = α ≫ e⁻¹ j`. Since `α ≫ e⁻¹ j ≠ 0`, `c = 1`. Both pieces are
  spanned by `α` and `β`.
- **`inHtilde_of_commute`**: let `α ≠ 0` have degree `p g`. Suppose `homAction α` commutes
  with `homAction v` for every `v` of degree `p k` and every `k` with `InH j k`. Then
  `InHtilde j g` holds, through `A = φ_α(g)`.
  Proof. For `k ∈ H(j)` take `β` of degree `p k = p(g⁻¹ k g)` fixing `e⁻¹ j`, with
  `j(φ_β(g⁻¹ k g) w) = π(g⁻¹ k g) j(w)`. Apply the commutation to `e⁻¹ j` and evaluate with
  `hom_inducedLiftHomEquiv_comp`.

## Degrees

`degreeHom : G →* Multiplicative ι` is `p` as a group homomorphism, and
`mem_comap_degreeHom` says `g ∈ comap degreeHom S ↔ p g ∈ S`. `relIndex_comap_degreeHom`:
relative indices of subgroups of degrees pull back along `p`, provided the larger subgroup
consists of values of `p`.

## Main theorem: `lineStabilizer`

Hypotheses: `H` open and normal, `ρ` irreducible with `rank ρ ≤ ℵ₀`, `DecidableEq ι`, and a
smooth `π` such that:

- `Hom(I, π)` is finite-dimensional;
- `hcyc`: every nonzero `φ : I → π` generates `Hom(I, π)` under `End I`;
- `hiso`: an `End I`-linear isomorphism `Hom(I, π ⊗ ω) ≃ Hom(I, π)` forces `π ⊗ ω ≅ π`, for
  characters `ω` with open kernel containing `H`;
- `hT`: `T` is the set of `g` with `ω g = 1` for every such `ω` with `π ⊗ ω ≅ π`;
- `hex`: some injective `j : ρ → π|_H` exists.

These are the hypotheses of the published `mem_radical_iff` and `surjective_homAction`.

Conclusion: the body of the target statement, with `H` for `⁰G` and `π`, `T` as given.
That is, a good `j` exists, and for every good `j` there are `m`, `H'` and `N` with
`rank Hom(ρ, π|_H) = m`, `H' = {g | InH j g}`, `N = {g | InN g}`, `T ≤ H' ≤ N`,
`[N : H'] = [H' : T] = m`, (VI.4.4.3), and the component statement.

Proof. Let `R = End I` with the grading `component` and the action `homAction` on
`M = Hom(I, π)`, and write `x = e⁻¹ j`.

1. `x ≠ 0` for injective `j`. Every nonzero `x` gives an injective `e x`. `homAction` is
   surjective (Burnside) and anti-multiplicative with `homAction 1 = 1`.
2. Every degree in the support is some `p g` (`exists_degree_eq`).
3. `InH j g ↔ p g ∈ stab x` (`inH_iff`), `InN g ↔ p g ∈ support` (`inN_iff`), and
   `g ∈ T ↔ p g ∈ radical` (`hT` and `mem_radical_iff`).
4. `InHtilde j g → p g ∈ perp (stab x)`: by `inN_of_inHtilde` and `inN_iff` the piece is
   nonzero; commutation comes from `mul_comm_of_inHtilde` and `homAction_mul`.
5. For good `j`, `perp (stab x) ⊆ stab x`: combine `inHtilde_of_commute` with goodness and
   step 3.
6. Existence of a good `j`: `exists_perp_subset_stab` gives `x ≠ 0` with
   `perp (stab x) ⊆ stab x`. Then `j = e x` is injective. It is good by steps 3 and 4.
7. For good `j`, take `m = finrank Hom(ρ, π|_H)`, `H' = comap degreeHom (stab x)` and
   `N = comap degreeHom support`. Then `T = comap degreeHom radical` by step 3, and
   `radical_le_stab`, `stab_le_support` give `T ≤ H' ≤ N`. The indices come from
   `relIndex_comap_degreeHom` (using step 2), `relIndex_stab_support`,
   `relIndex_radical_stab`, and `finrank Hom(I, π) = finrank Hom(ρ, π|_H)` via `e`.
8. (VI.4.4.3). For `t ∈ T`, `p t` is in the radical, so some `u` of degree `p t` has
   `homAction u = 1` (`exists_mem_map_eq_one`). By `hom_comp_symm_apply`,
   `ψ(φ_u(t) w) = π(t) ψ(w)` for every `ψ : ρ → π|_H`. If `j(w') = π(t) j(w)`, then
   `w' = φ_u(t) w` by injectivity of `j`, so `ψ(w') = π(t) ψ(w)`.
9. Components. Let `E` be irreducible and `T`-stable, and let `ψ ≠ 0` have image in `E`.
   `ψ` is injective. Its image `E'` is `T`-stable by step 8, since `T ≤ H'`. It is nonzero
   and contained in `E`, so `E' = E` by minimality. `ψ` is then a linear bijection
   `ρ ≃ E` (`LinearEquiv.ofBijective`), and it is `T`-equivariant by step 8.

## Relation to the source

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, preliminary remarks and
Lemma, printed pp.155–158 / PDF pp.161–164.

The statement proved is that of the Lemma, for an arbitrary open normal subgroup with a
degree map in place of `⁰G`. The proof differs from Renard's. Renard uses
`π ≃ ind_H^G ρ_H`, Proposition VI.3.2 (iii) adapted to `T` and `H`, the duality between tori
and lattices, and the adjunction (VI.4.4.4) with `ind_T^H ρ_T ≃ ⊕_ξ ρ_H ⊗ ξ`. Here
everything is read off the graded algebra `End(ind_H^G ρ)` acting on `Hom(ind_H^G ρ, π)`,
through the module `RankOneGradedLagrangian`. The good line is found by a minimal-index
argument rather than Renard's replacement of `W`. Normality of `H'` in `G` is neither
proved nor used.
