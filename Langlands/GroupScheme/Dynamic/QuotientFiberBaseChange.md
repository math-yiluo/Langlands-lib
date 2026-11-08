# Base change of the fibre criterion for dynamic parabolic quotients

Authors: Worker 254, Worker 266.

This module proves one lemma in the namespace `Langlands.GroupScheme`. It
imports only the Library module `Langlands.GroupScheme.Dynamic.BaseChange`.

## Main result

- `dynamicParabolicQuotient_fiber_baseChange`: let `b : S' ⟶ S` be any
  morphism of base schemes, `G` a group scheme over `S`,
  `χ : 𝔾_{m,S} ⟶ G` a cocharacter and `q : G.X ⟶ Q` a morphism over `S`.
  Assume that `q` satisfies the right-coset fibre criterion for the dynamic
  parabolic `P_G(χ)` (`Dynamic.parabolic χ`) on all test schemes `T` over
  `S`: for points `g, h : T ⟶ G.X`,
  `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ P_G(χ)(T)`. Then the base change
  `(Over.pullback b).map q : ((GroupScheme.baseChange b).obj G).X ⟶
  (Over.pullback b).obj Q` satisfies the same criterion for
  `Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ)` on all test schemes
  over `S'`.

There is no assumption on `b`, and no assumption on `q` beyond the criterion.

## Proof

The proof follows that of
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient.baseChange`. Fix `T`
over `S'` and points `g, h : T ⟶ G_{S'}`. The adjunction
`Over.mapPullbackAdj b` identifies maps `T ⟶ Q_{S'}` with maps from `T`,
regarded over `S`, to `Q`. By its naturality the two composites with the
base-changed `q` correspond to `baseChangePointsEquiv b G T g ≫ q` and
`baseChangePointsEquiv b G T h ≫ q`. The original criterion turns their
equality into membership of `(g_S)⁻¹ * h_S` in `P_G(χ)`. Here `g_S` and `h_S`
are the images of `g` and `h` under `baseChangePointsEquiv`.
`Dynamic.parabolic_baseChange` identifies `P_{G_{S'}}(χ_{S'})` with the base
change of the subgroup functor `P_G(χ)`. `SubgroupFunctor.mem_baseChange`,
together with multiplicativity of `baseChangePointsEquiv` (`map_mul`,
`map_inv`), gives membership of `g⁻¹ * h`.

## Provenance

This is an internal lemma for the formalization of CGP Proposition C.1.6
(Conrad, Gabber and Prasad, *Pseudo-reductive groups*, 2nd ed., printed
p.586). The source proof extends the ground field more than once, first to
`k_s` and then to `k̄`. Each time it uses tacitly that `G/P` base-changes to
`G_K/P_K` and that `P_G(λ)_K = P_{G_K}(λ_K)`. In the Library's quotient
interface, the first fact is this lemma. The second is
`Dynamic.parabolic_baseChange`.
