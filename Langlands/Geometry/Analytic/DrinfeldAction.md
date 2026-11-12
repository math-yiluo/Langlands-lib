# Projective linear transformations of Drinfeld's upper half space

Author: Worker 21.

This module takes an invertible matrix `γ ∈ GL_{d+1}(F)` and builds the map
`z ↦ γ · z` of Drinfeld's upper half space `Ω` (module
`DrinfeldUpperHalfSpace`) as a morphism of atlas presentations. The source and
target presentation is the exhaustion presentation
`exhaustionPresentation F K d` of `Ω` by the chain `V_0 ⊆ V_1 ⊆ ⋯` (module
`DrinfeldExhaustion`). The result is `presentationHom K γ`, an
`AffinoidAtlasPresentation.Hom`. Its data are:

- the continuous map `actionMap K γ : C(Ω, Ω)`;
- a monotone choice of target member for each member of the exhaustion;
- bounded pullbacks of functions between the chart algebras, compatible with
  the charts and with the restrictions.

The module does not prove the group law, the identity law, continuity in `γ`,
or the action on the localized category of analytic spaces (see Scope).

All declarations lie in `Langlands.Analytic`, in the namespaces
`AnalyticAffineSpace` and `DrinfeldUpperHalfSpace`. The hypotheses are those of
`DrinfeldUpperHalfSpace`: `F` is a nontrivially normed field, `K` is a
nontrivially normed, ultrametric and complete normed `F`-algebra, and `d : ℕ`.
From the shell estimates on, `F` has compact closed balls (`ProperSpace F`). The
statements about members of the exhaustion assume `NeZero d`, as the exhaustion
atlas does.

## Original sources and derived provenance

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`, printed
p.107 / PDF p.1: "Ω^d is a strict analytic space over K, on which PGL(d, K)
acts (see [1])." In Drinfeld's notation `Ω^d ⊆ ℙ^{d-1}`. Here `Ω ⊆ ℙ^d` has
dimension `d`, so the group is `PGL_{d+1}(F)`, represented by `GL_{d+1}(F)`.

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, §2, printed
p.88 / PDF p.14: "Furthermore, the natural action of GJ^ad ≃ PGL(n, F_v) on Ω
lifts naturally to an action of GJ on each of the Σ_N which commutes with the
action of C_v/C_v^{N,0} (for all this, see [Dr])." Harris's `Ω` has dimension
`n` and its points lie in `ℙ^n`.

The sources state that `PGL` acts and give no formula or analytic construction.
The construction below is derived. The action on points is the usual action of
matrices on homogeneous column vectors. With `ℓ_c = c_0 + Σ_i c_{i+1} Tᵢ` and the
point `z = (1 : z_1 : ⋯ : z_d)`, the `k`-th homogeneous coordinate of `γ z` is
`ℓ_{γ_k}(z)` for the `k`-th row `γ_k`. Dividing by the `0`-th coordinate gives
`Tᵢ ↦ ℓ_{γ_{i+1}} / ℓ_{γ_0}`. The analytic part is internal and works over the
chain atlas: it uses bounded inverses of `ℓ_{γ_0}` on Laurent charts, bounded
evaluation of Tate series, the universal property of rational domains, and
gluing along the net of members.

## Affine-linear functions

In `AnalyticAffineSpace`:

- `linearForm_add`, `linearForm_zero`, `linearForm_sum`: `c ↦ ℓ_c` is additive
  on the `m`-th polydisc algebra.
- `norm_linearForm_le`: if `‖cᵢ‖ ≤ B` for all `i`, then
  `‖ℓ_c‖ ≤ (d + 1) B ‖ϖ‖⁻ᵐ` in the `m`-th polydisc algebra.
- `disc_restriction_coordinate`: restriction between polydiscs sends the
  coordinate `Tᵢ` to `Tᵢ`.

In `DrinfeldUpperHalfSpace`, `coefficients F K d a` is the image in `K^{d+1}` of
a coefficient vector `a ∈ F^{d+1}`:

- `coefficients_vecMul`, `linearForm_vecMul`: `ℓ_{a ᵥ* g} = Σ_k a_k ℓ_{g_k}`,
  where `a ᵥ* g` is the row vector `a` times the matrix `g` and `g_k` is the
  `k`-th row of `g`.

## The inverse of a nonvanishing linear form on `V_N`

Fix `c ∈ F^{d+1}` with `c ≠ 0`.

- `half_threshold_le`: on `V_N`, every vector `a` of the shell satisfies
  `|ℓ_a| ≥ δ_N / 2`. This is the estimate from the proof of
  `exhaustion_subset_omega`: choose `b` in the net within `η_N` of `a`.
- `shellScale F d hc` is a chosen `t ≠ 0` with `t • c` in the shell
  (`shellScale_ne_zero`, `shellScale_smul_mem`).
- `lowerBound F d hc N = ‖t‖⁻¹ δ_N / 2` (written `r_N`). It is positive
  (`lowerBound_pos`), and `lowerBound_le` gives `|ℓ_c| ≥ r_N` at every point of
  `V_N`.
- `boundChart F K d hc N` is the Laurent chart `{r_N ≤ |ℓ_c|}` of the `N`-th
  polydisc. `hasImageIn_boundChart`: the chart `V_N` maps into it.
- `boundChartMap F K d hc N : O(boundChart) → O(V_N)` is the bounded map given by
  the universal property of the rational domain `boundChart`
  (`boundChartMap_comp_baseMap`).
- `boundFraction F K d hc N` is the fraction coordinate `1 / ℓ_c` of the Laurent
  chart, with `‖1 / ℓ_c‖ ≤ r_N⁻¹` (`norm_boundFraction_le`) and
  `ℓ_c · (1 / ℓ_c) = 1` (`boundFraction_equation`).
- `inverse F K d hc N` is the image of `1 / ℓ_c` in `O(V_N)`.
  `linearForm_mul_inverse`: `ℓ_c · inverse = 1` in `O(V_N)`.
  `norm_inverse_pow_le`: there is `C > 0` with
  `‖inverse ^ n‖ ≤ C r_N⁻ⁿ` for all `n`, where `C` comes from the bound of
  `boundChartMap`.

## The evaluation map of a matrix

Here `g : Fin (d + 1) → Fin (d + 1) → F` is a matrix given by its rows, with
`g 0 ≠ 0`.

- `rowBound g = Σ_k ‖g_k‖`. `norm_row_le_rowBound` bounds each row.
- `actionTuple K g hg N i = ℓ_{g_{i+1}} · inverse(ℓ_{g_0})` in `O(V_N)`, the
  image of `Tᵢ`.
- `inverseConst K g hg N` is the constant `C` of `norm_inverse_pow_le` for
  `c = g_0`. `norm_inverse_le`: `‖inverse‖ ≤ C r_N⁻¹`.
- `actionBound K g hg N = (d + 1) · rowBound g · ‖ϖ‖⁻ᴺ · C r_N⁻¹`.
  `norm_actionTuple_le`: each `actionTuple` has norm at most `actionBound`.
- `actionHom K g hg N n hn : O(D_n) → O(V_N)` is the bounded `K`-algebra map
  `Tᵢ ↦ ℓ_{g_{i+1}} / ℓ_{g_0}` from the `n`-th closed polydisc, defined when
  `actionBound ≤ ‖ϖ‖⁻ⁿ` (`hn`). It is evaluation of restricted series
  (`evaluateHom`), with monomial values bounded by the polyradius weights,
  passed to the quotient by the zero ideal of the polydisc presentation.
  `actionHom_coordinate` computes it on coordinates.
- `actionHom_linearForm`: `actionHom (ℓ_a) = ℓ_{a ᵥ* g} · inverse(ℓ_{g_0})`.
  Expand `ℓ_a` and use `ℓ_{g_0} · inverse = 1` for the constant term.

## Image points lie in `Ω`

- `inverse_apply_ne_zero`: every point `x` of `V_N` has `x(inverse) ≠ 0`, since
  `x(ℓ_{g_0}) x(inverse) = 1`.
- `baseMap_linearForm_ne_zero`: `x(ℓ_a) ≠ 0` for `a ≠ 0` and `x` in `V_N`,
  because `V_N ⊆ Ω`.
- `actionPoint K g hg N n hn x` is the point of the affine space obtained by
  pulling `x` back along `actionHom` and mapping it by the `n`-th polydisc
  chart. `linearNorm_actionPoint`:
  `|ℓ_a(g · x)| = |ℓ_{a ᵥ* g}(x)| · |inverse(x)|`.
- For an invertible `γ`: `vecMul_ne_zero` (`a ᵥ* γ ≠ 0` for `a ≠ 0`),
  `row_zero_ne_zero` (`γ_0 ≠ 0`), and `entries γ`, the entries of `γ` as a plain
  function (`entries_row_zero_ne_zero`, `vecMul_entries_ne_zero`).
- `actionPoint_mem_omega`: `γ · x ∈ Ω`. For `a ≠ 0` both factors in
  `linearNorm_actionPoint` are nonzero.

## Compatibility with the restrictions of the exhaustion

Here `U, V` are members of the exhaustion with `U ⊆ V`.

- `atlas_restriction_linearForm`, `atlas_restriction_coordinate`: restrictions of
  the polydisc atlas preserve `ℓ_c` and `Tᵢ`.
- `exhaustionRes K h : O(V) → O(U)` is the restriction of the existing
  inclusion `exhaustionInclusion`, typed in the chart algebras.
  `exhaustionRestriction_baseMap`: it sends `ℓ_c` to `ℓ_c`.
- `exhaustionRestriction_inverse`: it sends `inverse(ℓ_{g_0})` to
  `inverse(ℓ_{g_0})`, by uniqueness of inverses.
  `exhaustionRestriction_actionTuple` follows.
- `actionPoint_restriction`: the image point does not depend on the member of the
  exhaustion or on the polydisc used to compute it. Both evaluation maps agree
  after restriction to a common polydisc `D_m` (`hom_ext_coordinate`), and
  `chart_pull` compares the polydisc charts.
- `exists_radius_ge`, `actionLevel K g hg N` (the first `n` with
  `actionBound ≤ ‖ϖ‖⁻ⁿ`, by `Nat.find`), `actionLevel_spec`.
- `chartAction K g hg U x` is `actionPoint` at `actionLevel`.
  `continuous_chartAction`: it is continuous in `x`. `chartAction_restriction`:
  it is compatible with `exhaustionRes`.

## The continuous map `z ↦ γ · z` of `Ω`

- `exhaustionFamily` is the family of chart images of the exhaustion atlas, a net
  (`isNet_exhaustionFamily`). Each chart map is an embedding
  (`isEmbedding_exhaustionChartMap`). `exhaustionChartMap_res` gives the chart
  square for `exhaustionRes`.
- `memberIndex K W` is a chosen index whose chart image is the member `W`
  (`range_memberIndex`).
- `memberMap K γ W : C(W, Ω)` sends `w ∈ W` to `chartAction` of the chart
  preimage of `w` under the homeomorphism of the embedding.
  `memberMap_chart` computes it on chart points.
- `compatibleMaps K γ` collects the `memberMap`s as existing
  `AtlasTopology.CompatibleMaps`. Compatibility under `W ⊆ W'` follows from
  `chartAction_restriction`.
- `actionMap K γ : C(Ω, Ω)` is the gluing `AtlasTopology.IsNet.glue` of these
  maps along the net. `actionMap_chart`: on the chart point of `x` in the member
  `U`, its value is `chartAction K γ U x`.

## Target charts and pullbacks

Here `γ` is invertible and `U` is a member of the exhaustion.

- `exists_chartAction_subset`: the image of the chart of `U` is compact and lies
  in `Ω`, so it lies in some `V_N` (`exists_subset_exhaustion`).
- `targetLevel K γ U` is the first such `N` (`Nat.find`).
  `chartAction_mem_targetLevel`, and `targetLevel_mono` (monotone in `U`: by
  `chartAction_restriction`, the image of the chart of `U` lies in the image of
  the chart of a larger member).
- `targetIndex K γ U` is `V_{targetLevel}` as an index; it is monotone
  (`targetIndex_mono`), and `exhaustion_targetIndex_level` identifies its set.
- `sourceLevel K γ U = max (level of targetIndex) (actionLevel of U)`, with
  `le_sourceLevel` and `actionBound_le_sourceLevel`. On the polydisc
  `D_{sourceLevel}` both the evaluation map of `γ` and the target member are
  available.
- `targetDomain K γ U` is the target member as a domain of
  `D_{sourceLevel}` (existing `extendDomain` of the polydisc atlas).
  `hasImageIn_targetDomain`: pulling the points of `U` back along the
  evaluation map `actionHom : O(D_{sourceLevel}) → O(U)` gives points of the
  locus of `targetDomain`. This follows from `chartAction_mem_targetLevel` and
  `actionPoint_mono` (independence of the polydisc, from
  `actionHom_comp_restriction`).
- `pullback K γ U : O(target of U) → O(U)` is the bounded map given by the
  universal property of `targetDomain` (`pullback_comp_baseMap`).
  `pullback_coordinate`: it sends `Tᵢ` of the target chart to
  `ℓ_{γ_{i+1}} / ℓ_{γ_0}`. The auxiliary lemmas
  `pullback_targetDomain_coordinate` and `targetDomain_coordinate` compare the
  two descriptions of `Tᵢ`. `exhaustionRes_baseMap_restriction` and
  `exhaustionRes_coordinate` show that `exhaustionRes` sends `Tᵢ` to `Tᵢ`.
- `chart_pullback`: the target chart of the pulled-back point is
  `actionMap K γ` of the chart point.
- `pullback_restriction`: the pullbacks commute with restriction along `U ⊆ V`.
  Both sides are compared on the coordinates of `targetDomain` using the
  uniqueness part of its universal property (`represents.hom_ext`).

## The morphism of presentations

`presentationHom K γ : AffinoidAtlasPresentation.Hom (exhaustionPresentation F K d)
(exhaustionPresentation F K d)` has base map `actionMap K γ`, index map
`targetIndex K γ` (monotone by `targetIndex_mono` and
`range_exhaustionChartMap_subset_iff`), pullbacks `pullback K γ`, chart square
`chart_pullback`, and restriction square `pullback_restriction`.

## Scope

Proved here, for each fixed invertible `γ`: the continuous map `z ↦ γ · z` of
`Ω` and its structure as a morphism of atlas presentations. Not proved here:

- that `presentationHom` respects products of matrices and the identity matrix;
- that scalar matrices act trivially (the action factors through `PGL`);
- the resulting group homomorphism into automorphisms of `Ω` in the localized
  category of analytic spaces;
- continuity of the action in `γ`.

The index maps of `presentationHom (γ γ')` and of the composite differ in
general. A comparison of these morphisms therefore has to be made after
localization, or through the chosen-atlas equivalences.
