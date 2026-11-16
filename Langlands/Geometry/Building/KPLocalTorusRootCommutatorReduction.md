# Positive-depth torus commutators from valued rank-one coordinates

Module `Langlands.Geometry.Building.KPLocalTorusRootCommutatorReduction`.

The main theorem is

```
theorem kpLocalTorusRootCommutator_of_valuedRankOneCoordinates
    (hC : QuasiSplitValuedRankOneCoordinatesStatement.{u}) :
    KPLocalTorusRootCommutatorStatement.{u}
```

Assume valued rank-one coordinates exist (`QuasiSplitValuedRankOneCoordinatesStatement`).
Then a point `t` of the centralizer torus `Z(K)` that is congruent to `1` at depth `r`
under every geometric character moves `U_{a,x,s}` by commutators into the block
`U_{a,x,r+s} · U_{2a,x,r+s}`. This is KP Lemma 7.2.3 over `K = F^ur`, in the form of
`KPLocalTorusRootCommutatorStatement`. The route follows the rank-one computations in the
proof of KP Proposition 7.1.1 for quasi-split groups (the `SL_2` and `SU_3` cases,
printed pp. 239–240). The `SU_3` group law is the Library's `SU3Root.Parameters`
convention `(a₁, b₁)(a₂, b₂) = (a₁ + a₂, b₁ + b₂ + a₁ bar(a₂))`, after KP (2.7.2)
(printed p. 110).

The hypothesis is the published statement `QuasiSplitValuedRankOneCoordinatesStatement`.
This module does not prove it, so the theorem is a reduction.

## Published inputs

* `SU3RootScalingCommutator`:
  * `SU3Root.Parameters.scale_mul_inv_mem_filtration_product` writes
    `scale χ p · p⁻¹ = q · y`, with `q` in the root filtration at depth `r + s'` and `y`
    in the central filtration at depth `r + 2s'`, whenever `r ≤ w(χ - 1)` and `p` has
    depth `s'`;
  * `SU3Root.Parameters.scale_mul_inv_mem_centralFiltration` handles central `p`.
* `KPLocalCoordinateCharacterCongruence`: `coordinateCharacter_mem_unitFiltration`
  bounds characters over the coordinate field. If `t` lies in the geometric character
  congruence at depth `r`, then every character `χ` of `Z` over a finite separable
  coordinate field `M/K` satisfies `r ≤ w_M(χ(t) - 1)`, for the `K`-normalized Henselian
  valuation `w_M`.
* `SU3Root.henselianSeparableAddValuation_quadratic_bar`: `w_L` is invariant under the
  quadratic conjugation.

## Small helpers

* `coe_le_add_coe_iff_coe_sub_le`: `a ≤ X + c ↔ a - c ≤ X` in `WithTop ℝ`, for real
  `a, c`.
* `addValuation_nonneg_of_coe_le_sub_one`: if `0 ≤ r ≤ w(χ - 1)`, then `0 ≤ w(χ)`.

## Commutators in an apartment

For KP apartment data `D` (namespace `KPApartmentData`):

* `exists_val_eq_add_eval`: two apartment points `x, y` differ by a translation `v`,
  i.e. `x_a(g) = y_a(g) + a(v)` for all `a, g` (`equipollent_of_mem`, `vadd_apply`).
* `commutator_mem_filtration_of_fieldScaling`: take field coordinates
  `e : E → U_b(k)` with `x_b(e(τ)) = w(τ) + β`. Suppose `z e(τ) z⁻¹ = e(χτ)` and
  `r ≤ w(χ - 1)`. Then for `u ∈ U_{b,x,s}`, `z u z⁻¹ u⁻¹ = e((χ - 1)τ)` lies in
  `U_{b,x,r+s}`.
* `commutator_mem_filtrationBlock_of_unitaryScaling`: take `0 ≤ s` and unitary
  coordinates `e : Parameters c → U_b(k)` whose central parameters give exactly
  `U_{2b}(k)`, with `x_b(e(p)) = depthA_w(p) + β` and `x_{2b}(e(q)) = w(q.second) + 2β`
  on central `q`. Suppose `z e(p) z⁻¹ = e(scale χ p)` and `r ≤ w(χ - 1)`. Let
  `u = e(p) ∈ U_{b,x,s}`, so `p` has depth `s - β`. The commutator is `e(q) · e(y)` with
  `scale χ p · p⁻¹ = q · y` as above. Then `e(q) ∈ U_{b,x,r+s}`, and
  `e(y) ∈ U_{2b,x,r+s}` because `w(y.second) + 2β ≥ r + 2(s - β) + 2β ≥ r + s`. So the
  commutator lies in `filtrationBlock x (fun _ => r + s) b`.
* `commutator_mem_filtrationBlock_double_of_unitaryScaling`: the same coordinates for the
  divisible root `2b`, with `x_{2b}(e(q)) = w(q.second) + γ` on central `q`, and
  `0 ≤ r`. For central `q` of depth `s - γ`, the commutator `e(scale χ q · q⁻¹)` is
  central of depth `r + s - γ`. It lies in `U_{2b,x,r+s}`, and so in the block of `2b`
  (with trivial second factor).

## The case analysis over `K = F^ur`

In namespace `KPLocalTorusRootCommutator`, for `B : MaximalUnramified.BuildingData F H`:

* `exists_indivisible_eq_or_double`: every relative root `a` equals an indivisible root
  `b`, or equals `2 • b` for an indivisible root `b`, with `2 • b` a root. The proof
  uses `HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem` for
  `B.hasOppositeFactorPairs`. Its other inputs are smoothness from
  `B.isConnectedReductive` and the split torus `B.S`.
* `commutator_mem_filtration_sl2` (`2b` not a root): uses `ValuedSL2RootCoordinates`.
* `commutator_mem_filtrationBlock_su3` (`2b` a root, `a = b`): uses
  `ValuedSU3RootCoordinates`.
* `commutator_mem_filtrationBlock_double` (`a = 2b`): uses the same `SU_3` coordinates of
  `b`.

In each case the apartment point `x` is a translate of the coordinate origin by `v`, and
`β = b(v)` (with `(2b)(v) = 2β`, `eval_nsmul_char`). The depth fields `depth_positive`
and `depth_double_positive` give the depth hypotheses. The equivariance field
`conjugation` of the positive coordinates gives the action of `z = j(t)` by the
coordinate character `χ`. The bound `r ≤ w(χ(t) - 1)` comes from
`coordinateCharacter_mem_unitFiltration`, with the published Henselian witness
`MaximalUnramified.valuationSubring_isHenselian`.

`kpLocalTorusRootCommutator_of_valuedRankOneCoordinates` splits `a` with
`exists_indivisible_eq_or_double`, obtains the coordinates of `b` from `hC`, and applies
the matching case. In the `SL_2` case the block's second factor is `1`. The hypothesis
`0 < r` of the target statement is not used.

## Provenance

The module is a derived formalization step and has no separate literature counterpart.
It combines the published interface statement, the published `SU_3` scaling-commutator
computation and the published character transport. The case split matches the cases
`SL_2`, `SU_3` and the divisible root in KP's proof.
