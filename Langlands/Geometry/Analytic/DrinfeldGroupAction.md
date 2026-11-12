# The action of `GL_{d+1}(F)` on Drinfeld's upper half space

Author: Worker 21.

The module `DrinfeldAction` gives, for each invertible matrix `γ`, the map
`z ↦ γ · z` of Drinfeld's upper half space `Ω` as a morphism of atlas
presentations, `presentationHom K γ`. This module proves the group law and the
identity law for these maps and builds the action of `GL_{d+1}(F)` on `Ω`:

- `omegaAction F K d`, an object of Mathlib's category
  `Action (LocalizedCategory) GL_{d+1}(F)`. Its underlying analytic space is
  the localized image of the saturation of the exhaustion presentation of `Ω`.
  Its action homomorphism is `γ ↦ ρ(γ)`.
- The underlying continuous map of `ρ(γ)` is `actionMap K γ`
  (`localizedSpaceFunctor_map_omegaAction`), and the underlying space is
  Hausdorff.

Mathlib's `Action.ρAut` turns the action into a homomorphism
`GL_{d+1}(F) →* Aut(Ω)`, the shape `G → G(X)` in Berkovich's definition below.
Continuity of this homomorphism (`IsContinuousAction`) is not proved here, so
`Ω` is not yet a `GSpace` (see Scope).

All declarations lie in `Langlands.Analytic`. The hypotheses on `F`, `K` and
`d` are those of `DrinfeldUpperHalfSpace` and `DrinfeldExhaustion`: `F` is a
nontrivially normed field with compact closed balls (`ProperSpace F`), `K` is a
nontrivially normed, ultrametric and complete normed `F`-algebra. The
statements about members of the exhaustion assume `NeZero d`.

## Original sources and derived provenance

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`, printed
p.107 / PDF p.1: "Ω^d is a strict analytic space over K, on which PGL(d, K)
acts (see [1])." In Drinfeld's notation `Ω^d ⊆ ℙ^{d-1}`. Here `Ω ⊆ ℙ^d`, so
the group is `PGL_{d+1}(F)`, and the action is defined on `GL_{d+1}(F)`.

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, §2, printed
p.88 / PDF p.14: "Furthermore, the natural action of GJ^ad ≃ PGL(n, F_v) on Ω
lifts naturally to an action of GJ on each of the Σ_N which commutes with the
action of C_v/C_v^{N,0} (for all this, see [Dr])."

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.1,
printed p.1: "let G(X) denote the group of automorphisms of X"; printed p.2:
"We say that the action of a topological group G on an analytic space is
continuous if the induced homomorphism G → G(X) is continuous." This module
constructs the homomorphism; its continuity is not treated.

The sources give no analytic construction. The construction is derived: it
works on the chain atlas of `Ω` from `DrinfeldExhaustion` and with the explicit
pullbacks of `DrinfeldAction`.

## Strong maps into atlases with totally ordered charts

These results are general; they lie in the namespaces `IndexedAffinoidAtlas`
and `AffinoidAtlasPresentation`.

- `HasChainCharts a`: any two chart images of the atlas `a` are comparable for
  inclusion. `HasChainCharts.hasDirectedCharts`: such an atlas has directed
  charts in the sense of the existing `HasDirectedCharts`.
- `StrongHom.hasCoherentPullbacks_of_chain`: every strong map into an atlas
  with chain charts has coherent pullbacks (`HasCoherentPullbacks`). Of two
  admissible targets `j, k`, one contains the other, say `j ⊆ k`. Then the
  pullback to `k` is the pullback to `j` followed by the restriction from `k`
  to `j` (`restriction_comm`). The coherence identity then follows from
  `restriction_comp`, and in the case `k ⊆ j` from the cancellation
  `restriction_hom_ext`.
- `CompatibleStrongHom.ofChain f hb` is the existing directed extension
  `StrongHom.ofDirected` of a chosen-target map `f`, with this coherence. It is
  a morphism of the existing category `CompatibleAtlasPresentation`.
  `ofChain_baseMap`; `ofChain_pullback_selected` (at the selected target the
  pullback is `f.pullback`); `ofChain_pullback_upper` (at a larger target it
  is `f.pullback` followed by restriction).

## Pullbacks with prescribed coordinates

In `DrinfeldUpperHalfSpace`, for a matrix `g` given by its rows with `g_0 ≠ 0`:

- `map_linearForm_of_coordinate`: a bounded map out of a polydisc algebra that
  sends each `Tᵢ` to `ℓ_{g_{i+1}} / ℓ_{g_0}` sends `ℓ_a` to
  `ℓ_{a g} / ℓ_{g_0}`. The proof is the one of `actionHom_linearForm`.
- `eq_inverse_of_mul_eq_one`: an inverse of `ℓ_c` in the chart algebra of `V_N`
  equals `inverse` (inverses in a commutative ring are unique).
- `IsActionPullback K g hg U T φ`: the bounded map
  `φ : O(T) → O(U)` between chart algebras of members of the exhaustion sends
  each coordinate `Tᵢ` of `T` to `ℓ_{g_{i+1}} / ℓ_{g_0}` on `U`.
  - `IsActionPullback.eq`: there is at most one such map. Two maps that agree
    on the coordinates agree after the structure map of the rational domain `T`
    (`hom_ext_coordinate`), hence agree (`Represents.hom_ext`).
  - `IsActionPullback.comp_res`: precomposition with the restriction to a
    larger target member.
  - `IsActionPullback.comp`: the pullback along `g'` composed with the pullback
    along `g` is the pullback along the matrix whose rows are `g_k g'`, that is
    the product `g g'`. The composite sends `Tᵢ` to
    `(ℓ_{g_{i+1} g'} / ℓ_{g'_0}) · (ℓ_{g_0 g'} / ℓ_{g'_0})⁻¹`, which equals
    `ℓ_{g_{i+1} g'} / ℓ_{g_0 g'}` by `eq_inverse_of_mul_eq_one`.
- The identity matrix: `coefficients_entries_one` (its rows are the standard
  basis vectors), `linearForm_single_zero` (`ℓ_{e_0} = 1`),
  `linearForm_single_succ` (`ℓ_{e_{i+1}} = Tᵢ`), `inverse_one`,
  `actionTuple_one`, and `isActionPullback_id` (the identity map is the
  pullback along the identity matrix).
- `chart_eq_chartAction`: a map out of the `m`-th polydisc algebra with these
  coordinate values computes the image point `chartAction K g hg U x`. Both maps
  agree after restriction to a common polydisc (`chart_pull`).
  `IsActionPullback.chart_eq` is the case of a pullback.
- `mem_exhaustionChartMap`, `exists_exhaustionChartMap_eq`: chart points of a
  member lie in it, and every point of `Ω` is a chart point of some member.

## Invertible matrices

For `γ, γ' ∈ GL_{d+1}(F)`:

- `entries_mul`: the rows of `γ γ'` are `γ_k γ'`.
- `pullback_isActionPullback`: the pullback of `presentationHom K γ` has the
  prescribed coordinates (`pullback_coordinate`).
- `isActionPullback_pullback_comp`: the pullback of `γ'` followed by the
  pullback of `γ` is a pullback for `γ γ'`.
- `targetIndex_subset`: the chosen target of a member lies in every member that
  receives a pullback with these coordinates (minimality of `targetLevel`).
- `actionMap_mul`: `(γ γ') · z = γ · (γ' · z)`. `actionMap_one`: `1 · z = z`.

## The action

- `exhaustionAtlas_hasChainCharts`: the exhaustion atlas has chain charts,
  because the members `V_N` increase.
- `compatiblePresentation F K d` is the exhaustion presentation of `Ω` as an
  object of `CompatibleAtlasPresentation`.
- `compatibleHom K γ := ofChain (presentationHom K γ)`, with
  `compatibleHom_baseMap`.
- `compatibleHom_one`: `compatibleHom K 1 = 𝟙`. `compatibleHom_mul`:
  `compatibleHom K (γ γ') = compatibleHom K γ' ≫ compatibleHom K γ`. Both use the
  existing `CompatibleStrongHom.ext_of_pullback`: the base maps agree, and on
  each source chart one admissible pullback agrees. That pullback is computed
  by `ofChain_pullback_upper`, `ofChain_pullback_selected` and the existing
  `comp_pullback`, and compared by `IsActionPullback.eq`.
- `compatibleAction K : GL_{d+1}(F) →* End (compatiblePresentation F K d)`. In
  Mathlib `x * y = y ≫ x` in `End`, so this is a left action.
- `omegaAction F K d` is the image of `compatibleAction` under the existing
  functor `saturationFunctor ⋙ localizationFunctor`, by Mathlib's
  `Functor.mapAction`. `omegaAction_V` and `omegaAction_ρ` record its object
  and morphisms. `localizedSpaceFunctor_map_omegaAction`: the underlying
  continuous map of `ρ(γ)` is `actionMap K γ`. The instance `T2Space` for the
  underlying space holds because `Ω` is Hausdorff.

## Scope

Not proved here:

- continuity of `(omegaAction F K d).ρAut` in the sense of
  `IsContinuousAction`, so `Ω` is not yet a `GSpace`. This needs, for every
  test triple `(U, f, t)` of the saturated atlas, that matrices close to `1`
  map the affinoid domain `U` onto itself and move `f` by at most `t`;
- that scalar matrices act trivially, so that the action factors through
  `PGL_{d+1}(F)`;
- the comparison of this presentation of `Ω` with
  `DrinfeldUpperHalfSpace.presentation` (all rational domains of polydiscs
  inside `Ω`).
