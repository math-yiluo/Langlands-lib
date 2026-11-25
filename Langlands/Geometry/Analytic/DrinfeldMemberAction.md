# Norm-continuous actions of member stabilizers on the chart algebras of `V_N`

This internal supporting module is part of the proof of
`OmegaActionContinuityStatement` (module `DrinfeldActionContinuityProof`). For
each member `V` of the exhaustion `V_0 ⊆ V_1 ⊆ ⋯` of Drinfeld's upper half space
`Ω` (module `DrinfeldExhaustion`) it constructs the open subgroup of
`GL_{d+1}(F)` preserving `V` and an action of that subgroup on the chart algebra
`O(V)` of `V` by bounded automorphisms whose orbits are continuous for the
quotient norm. All declarations are in
`Langlands.Analytic.DrinfeldUpperHalfSpace`; the hypotheses on `F`, `K` and `d`
are those of `DrinfeldGroupAction` (`ProperSpace F`; `K` a complete ultrametric
nontrivially normed field and normed `F`-algebra; `NeZero d` wherever the
exhaustion atlas and its chart maps are used). `GL_{d+1}(F)` has Mathlib's topology on units of the matrix
algebra; it is a topological group (`Mathlib.Topology.Algebra.Group.Units`), and
so is every subgroup.

## Continuity of the coordinate images in the matrix

- `continuous_coefficients`, `continuous_entries_row`, `continuous_entries`,
  `continuous_linearForm`: the coefficient map `F^{d+1} → K^{d+1}`, the rows of
  `γ`, and `c ↦ ℓ_c = c_0 + Σ_i c_{i+1} T_i` in a polydisc algebra are continuous.
- `inverse_eq_ringInverse`: the Library's inverse of `ℓ_c` in `O(V_N)` is
  `Ring.inverse` of the image of `ℓ_c`, because `ℓ_c · inverse = 1`
  (`linearForm_mul_inverse`) in a commutative ring.
- `continuous_baseMap_linearForm`, `continuous_inverse_entries`: the image of
  `ℓ_{c(γ)}` in `O(V_N)` is continuous in `γ` for continuous `c`, and so is the
  inverse of `ℓ_{γ_0}`, since ring inversion is continuous at units of the
  complete normed ring `O(V_N)` (`NormedRing.inverse_continuousAt`).
- `continuous_actionTuple`: the Library's coordinate images
  `actionTuple = ℓ_{γ_{i+1}} · ℓ_{γ_0}^{-1}` are continuous in `γ`.
- `continuous_linearForm_vecMul_mul_inverse`: so are `ℓ_{bγ} · ℓ_{γ_0}^{-1}` for
  fixed `b ∈ F^{d+1}`; `vecMul_entries_one` evaluates them at `γ = 1`.

## Near the identity a matrix maps each member into itself

- `discEvaluation K N t ht`: the bounded evaluation of the `N`-th polydisc
  algebra at a tuple `t` of norms at most the radius `‖ϖ‖^{-N}`, built as the
  Library's `actionHom` (evaluation of restricted series passed to the zero
  quotient); `discEvaluation_coordinate` computes it on coordinates.
- `mapsTo_of_isActionPullback`: if `γ` has a pullback `O(V) → O(V)` with the
  coordinates of `γ` (`IsActionPullback`), then `γ` maps `V` into `V`. Points of
  `V` are chart points; `actionMap_chart` and `IsActionPullback.chart_eq`
  identify their images with chart points of `V`.
- `eventually_exists_isActionPullback`: for `γ` near `1` such a pullback exists.
  With `N` the level of `V`:
  1. At `γ = 1` the coordinate images are the coordinates `T_i` of `O(V_N)`
     (`actionTuple_one`), of norm at most the radius. By continuity and the
     ultrametric inequality (`eventually_coordinates_norm_le`), the norms stay at
     most the radius near `1`, so the evaluation `χ_γ = discEvaluation` exists.
  2. For each of the finitely many `b` in the net defining `V_N`, continuity
     gives `‖ℓ_{bγ}·ℓ_{γ_0}^{-1} − ℓ_b‖ < δ_N` near `1`, where `δ_N` is the
     threshold of `V_N`.
  3. For a point `x` of `O(V_N)`, `x(ℓ_b) ≥ δ_N` (the rational-chart range
     clause and `mem_locus_exhaustionChart`), and
     `x(χ_γ(ℓ_b)) = x(ℓ_{bγ}·ℓ_{γ_0}^{-1})` (`map_linearForm_of_coordinate`).
     Since `x ≤ ‖·‖`, the difference has `x`-value `< δ_N ≤ x(ℓ_b)`, so the
     nonarchimedean property of `x` gives `x(χ_γ(ℓ_b)) = x(ℓ_b) ≥ δ_N`. Hence
     `χ_γ` has spectral image in the locus of the rational chart `V_N`.
  4. The universal property of that rational chart factors `χ_γ` through
     `O(V_N)`; the factorization has the coordinates of `γ`.
- `eventually_mapsTo`: consequently, for `γ` near `1`, `γ` maps `V` into `V`.

## The stabilizer of a member

- `memberStabilizer K V`: the subgroup of all `γ` with
  `γ · z ∈ V ↔ z ∈ V` for every `z ∈ Ω`. The subgroup laws follow from
  `actionMap_mul` and `actionMap_one`.
- `memberStabilizer_mem_nhds`, `isOpen_memberStabilizer`: it contains every `γ`
  such that both `γ` and `γ⁻¹` map `V` into `V`, hence a neighbourhood of `1`
  (`eventually_mapsTo` and continuity of inversion), and a subgroup that is a
  neighbourhood of `1` is open.

## The pullback from a preserved member to itself

- `targetIndex_subset_of_mem`: for `γ` in the stabilizer, the Library's chosen
  target member of `V` (the first member containing the image of `V`) lies in
  `V`, by minimality of `targetLevel`.
- `selfPullback K V γ hγ`: with `W = targetIndex K γ V`, the composite
  `O(V) → O(W) → O(V)` of the bounded restriction `exhaustionRes : O(V) → O(W)`
  (first) and the Library's selected pullback `pullback K γ V : O(W) → O(V)`
  (second); in Lean, `(pullback K γ V).comp (exhaustionRes K _)`.
  `selfPullback_isActionPullback` records that it has the coordinates of `γ`; by
  uniqueness (`IsActionPullback.eq`) it equals every such map
  (`selfPullback_eq_of_isActionPullback`).
- `selfPullback_comp`, `selfPullback_one`, `selfPullback_congr`: writing `P_γ`
  for `selfPullback` along `γ`, pullbacks are contravariant:
  `P_(γγ') = P_γ' ∘ P_γ`, that is, on sections the pullback along `γ` acts first
  and the pullback along `γ'` second (`IsActionPullback.comp`, `entries_mul`).
  The identity matrix gives the identity (`isActionPullback_id`).
- `actionMap_exhaustionChartMap_selfPullback`: the chart point of the pulled-back
  seminorm is `γ` applied to the chart point.

## The action on the chart algebra

- `memberAut K V γ`: the bounded automorphism of `O(V)` with forward map the
  pullback along `γ⁻¹` and inverse the pullback along `γ`. With this convention
  `memberAction K V : memberStabilizer K V →* Aut O(V)` is a group homomorphism
  (`memberAction_hom`, `memberAction_inv`): by the contravariance above,
  `P_((γγ')⁻¹) = P_(γ'⁻¹γ⁻¹) = P_(γ⁻¹) ∘ P_(γ'⁻¹)`, which is the forward map of
  the product `memberAut γ * memberAut γ'` (`aut_mul_hom`). In the Library's
  action of `Aut O(V)` on spectra, `g • x = x ∘ g.inv`, so `memberAction γ • x`
  is the point `γ · x`.
- `aut_mul_hom`, `aut_one_hom_apply`: the forward map of a product of
  automorphisms is the composite, and the unit acts as the identity.
- `norm_baseMap_coordinate_le`, `continuous_val_inv`: auxiliary bounds and
  continuity of `g ↦ g⁻¹` into `GL_{d+1}(F)`.
- `continuousAt_memberAction_baseMap`: for each `a` of the polydisc algebra,
  `g ↦ memberAction g (ℓ(a))` is continuous at `1`, where `ℓ` is the structural
  map of the rational chart `V`. On coordinates it is `g ↦ actionTuple(g⁻¹)`, and
  the Library's `continuousAt_map_of_coordinates` extends coordinate continuity
  to all sections, using the center bound at `g = 1`.
- `continuous_memberAction`: every forward orbit `g ↦ memberAction g (a)`,
  `a ∈ O(V)`, is continuous for the quotient norm. The rational-chart coordinate
  theorem `RationalChart.continuousAt_map_coordinates` gives continuity at `1` on
  all coordinates of `O(V)`, `continuousAt_map_of_coordinates` extends it to
  every section, and `continuous_map_of_continuousAt_one` translates it along
  the group.

## Provenance and scope

This is internal derived content. It uses the Library's construction of the
action (`DrinfeldAction`, `DrinfeldGroupAction`), its exhaustion
(`DrinfeldExhaustion`) and its norm-continuity tools for presented affinoid
algebras (`CoordinateContinuity`, `RationalNormSectionContinuity`). The estimate
in `eventually_exists_isActionPullback` is the ultrametric argument suggested in
the statement's Markdown (for `γ` close to `1` the linear forms `ℓ_b` keep their
absolute values on `V_N`). The module does not assert continuity of the action
on `Ω` itself; that is proved in `DrinfeldActionContinuityProof`.
