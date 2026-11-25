# The metaplectic group of a model of the Heisenberg representation

**GKT §2.1.2** (the group `Mp(W)^{ℂˣ}_{ψ,S}` of pairs, Lemma 2.1, p. 48; the canonical projection
and the Weil representation, diagram (2.3), p. 48; `Mp(W)^{ℂ¹}_{ψ,S}`, p. 49), **Proposition 6.8 (1)**
(the change of model), **Definition 13.15** (`ω_{ψ,s} = ω_ψ ∘ s`, p. 399) and §12.2.1 (twisting a
splitting by a character).

The module `Langlands.Theta.Metaplectic.Defs` defines the metaplectic group as the book's group of
pairs `(g, M)` of a model of the Heisenberg representation, its projection to the symplectic group,
its Weil representation, the lifts of representations normalizing the model, and splittings.

## Content

Let `R` be a commutative ring with `⅟2`, `W` an `R`-module, `B` a bilinear form on `W`, and `ρ` a
representation of `HeisenbergGroup B` on a complex vector space `S`. The isometry group
`Sp(W) = LinearMap.BilinForm.isometryGroup B` acts on the Heisenberg group by
`g · (w, t) = (g w, t)` (`HeisenbergGroup.isometryAction`, GKT (2.1)).

- `IsMetaplecticPair ρ g M`: the relation (2.2), `M ∘ ρ(h) = ρ(g · h) ∘ M` for all `h`.
- `MetaplecticGroup ρ : Subgroup (Sp(W) × (S ≃ₗ[ℂ] S))`: the pairs satisfying (2.2) (Lemma 2.1:
  a subgroup). For a smooth irreducible `ρ` with central character `ψ` over a nonarchimedean local
  field this is `Mp(W)^{ℂˣ}_{ψ,S}`; no hypothesis is needed for the definition.
- `MetaplecticGroup.proj ρ`, `(g, M) ↦ g`, the canonical projection `p`, and
  `MetaplecticGroup.weil ρ : Representation ℂ (MetaplecticGroup ρ) S`, `(g, M) ↦ M`, the Weil
  representation `ω_{ψ,S}`; `weil_normalizes`: `ω_{ψ,S}` normalizes `ρ` along `p`.
- `MetaplecticGroup.scalar ρ : ℂˣ →* MetaplecticGroup ρ`, `z ↦ (1, z)`, central
  (`scalar_mem_center`, `scalar_mul_comm`), injective for `S ≠ 0` (`scalar_injective`).
- `MetaplecticGroup.unitary ρ inner`: for a sesquilinear form `inner` on `S`, the pairs whose
  operator preserves it. For the invariant Hermitian form of the model this is the book's
  `Mp(W)^{ℂ¹}_{ψ,S}` (p. 49: the book's `U(S)` is "unitarizable" since `S` is not complete; here no
  completion is used). `MetaplecticGroup.circle ρ inner : Circle →* unitary ρ inner`.
- `MetaplecticGroup.lift ρ ι ω h`: for a homomorphism `ι : G →* Sp(W)` and a representation `ω`
  of `G` on `S` with `Normalizes ρ ((isometryAction B).comp ι) ω`, the homomorphism
  `g ↦ (ι g, ω g)`; `proj_comp_lift`, `weil_comp_lift`. (`reprLinearEquiv ω g` is `ω g` as a linear
  automorphism.)
- `MetaplecticGroup.congr e : MetaplecticGroup ρ ≃* MetaplecticGroup ρ'` for an isomorphism of
  representations `e : ρ ≃ ρ'`: `(g, M) ↦ (g, e M e⁻¹)`; `proj_congr`, `weil_congr` (the Weil
  representations correspond, GKT Proposition 9.2). Independence of `e` is
  `MetaplecticGroup.congr_eq` (`Langlands.Theta.Metaplectic.Exact`).
- `MetaplecticGroup.Splitting ρ ι`: a homomorphism `G →* MetaplecticGroup ρ` lifting `ι` (fields
  `toMonoidHom`, `proj_comp`); `Splitting.weil s = ω_ψ ∘ s` (Definition 13.15), which normalizes
  `ρ` along `ι` (`Splitting.weil_normalizes`); `Splitting.ofNormalizes ω h` with
  `weil_ofNormalizes` (every normalizing representation comes from a splitting) and `ext_weil` (a
  splitting is determined by its Weil representation); `Splitting.twist s α`, `g ↦ α(g) · s(g)`
  for a character `α : G →* ℂˣ`, with `weil_twist`; `Splitting.comp s f`, the splitting `s ∘ f` of
  `ι ∘ f` for a homomorphism `f`, with `weil_comp`.

The book's realizations of the metaplectic group by cocycles (chapter 6), and the "collective"
statements over all realizations, are not here; in the realization by pairs a splitting over `G` is
literally a representation of `G` normalizing the model, which is what the Library's constructions
produce.

## Declarations

- `Langlands.Theta.IsMetaplecticPair`, `Langlands.Theta.MetaplecticGroup`,
  `Langlands.Theta.reprLinearEquiv`.
- In `Langlands.Theta.MetaplecticGroup`: `mem_iff`, `apply_apply`, `ext`, `proj`, `proj_apply`,
  `weil`, `weil_apply`, `weil_normalizes`, `scalar`, `proj_scalar`, `weil_scalar`,
  `scalar_mem_center`, `scalar_mul_comm`, `scalar_injective`, `unitary`, `mem_unitary_iff`, `circle`,
  `lift`, `proj_comp_lift`, `weil_comp_lift`, `proj_lift`, `weil_lift`, `congr`, `proj_congr`,
  `weil_congr`.
- `Splitting` (structure), `Splitting.ext`, `Splitting.proj_apply`, `Splitting.weil`,
  `Splitting.weil_apply`, `Splitting.weil_normalizes`, `Splitting.ofNormalizes`,
  `Splitting.weil_ofNormalizes`, `Splitting.ext_weil`, `Splitting.twist`, `Splitting.weil_twist`,
  `Splitting.comp`, `Splitting.weil_comp`.

## Dependencies

`Langlands.Theta.Heisenberg.Representation` (and through it `Heisenberg.Basic`,
`LinearAlgebra.Symplectic`); Mathlib: `Analysis.Complex.Circle`,
`RepresentationTheory.Intertwining`, `LinearAlgebra.SesquilinearForm.Basic`.
