# Finite orbits of the Galois coefficient action on the unramified building

Author: Worker 47 (Task 6502).

Let `F` be a non-archimedean local field, `K = inertiaFixedField F` its maximal unramified
extension, and `G` an affine group scheme over `F`. Let
`C : MaximalUnramified.BuildingData F (baseChanged F K G)` be an arbitrary supplied building
datum. The module `FieldIsoCoefficientChart` assembles the per-`σ` coefficient charts into
`coefficientActionData C`. This module defines the resulting action on `C.ReducedBuilding`
and proves that all its orbits are finite.

## Statements

- `finite_range_of_fixingSubgroup`: let `ρ : Aut(K/k) →* Perm X` be an action and `z` a point
  fixed by the fixing subgroup of a finite-dimensional intermediate field `E`. Then the orbit
  of `z` is finite. Two automorphisms with the same restriction to `E` give the same image of
  `z`, and there are finitely many `k`-embeddings `E → K`. (This is the pattern of the
  published `exists_galoisFixed_of_isAlgebraic`.)
- `unitsCoeff_map`: `σ⁻¹ ∘ σ = id` on units.
- `torus_compat_of_cocharacters`: let `ν_j` be finitely many cocharacters of the torus of `C`
  that generate its rational points, and suppose that `σ(i(ν_j(t))) = i(ν_j(σ t))` for all `j`
  and `t`. Then `σ` satisfies the torus hypothesis of `CoefficientChartFixing`: for every
  torus point `t` there is `t'` with `σ(i t) = i t'` and `σ⁻¹(χ(t')) = χ(t)` for all
  characters `χ`. Write `t = ∏ ν_j(x_j)` and take `t' = ∏ ν_j(σ x_j)`. The first identity is
  proved by induction over the product, because `G(K)` is not commutative. The second follows
  from `χ(ν_j(x)) = x^{⟨χ, ν_j⟩}`.
- `coefficientActionData_action_mk`, `coefficientActionData_action_mk_eq`: the action on a
  class `[(g, x)]` is `[(σ(g) c_σ, a_σ x)]`. Hence `[(g, x)]` is fixed when `σ(g) = g` and
  `c_σ • [a_σ x] = [x]`.
- `coefficientAction_finite_orbit`: assume `G` is locally of finite type. Then for every
  `z : C.ReducedBuilding` the set `{(coefficientActionData C).action σ z}` is finite. Write
  `z = [(g, x)]` and construct a finite intermediate field as follows:
  - Generating cocharacters `ν_j` of the split torus come from
    `IsSplitTorus.exists_cocharacterPoints_prod`. A first field `E₁` makes `σ` commute with
    the cocharacters `ν_j ≫ i` (`exists_finite_fixing_cocharacterValues`).
  - For every relative root `α` (finitely many, `IsSplitTorus.finite_relativeRoots`), choose
    `u_α ∈ U_α(K)` with `x_α(u_α) ≠ ⊤`. A second field `E₂` fixes `g` and every `u_α`
    (`exists_finite_fixing_rationalPoints`).
  - For `σ` fixing `E₁ ⊔ E₂`, `torus_compat_of_cocharacters` applies to `σ`, and also to `σ⁻¹`,
    which gives surjectivity on the torus. `CoefficientChart.c_smul_apartment_a_eq` applied to
    the chart `coefficientChart C σ` then shows that `σ` fixes `[(g, x)]`.

  Finally `finite_range_of_fixingSubgroup` gives finiteness.
- `coefficientAction C : Aut(K/F) →* Perm C.ReducedBuilding` is the action itself, defined as
  `(coefficientActionData C).action`. It is the declaration of this unit. Two further
  statements:
  - `coefficientAction_smul`: semilinearity for the rational-point action,
    `coefficientAction C σ (g • z) = rationalConjugate F K G σ g • coefficientAction C σ z`.
  - `coefficientAction_finite_range`: finite orbits.

  Together with the published isometry criterion
  `ApartmentQuotient.MovingSemilinearActionData.action_isometry` and the root-norm identity
  `CoefficientChart.norm_vsub`, these are the coefficient-action parts of
  `UnramifiedSemilinearMetricActionStatement`.

## Provenance

This is internal infrastructure for Task 6502. Finiteness of Galois orbits on the building of
an unramified group is standard. Every point lies in the apartment of a maximal split torus;
the torus, a point of `G(K)`, and finitely many root-group elements are defined over a finite
unramified extension `E`, and `Gal(K/E)` then fixes the point. The Lean proof follows this route
through cocharacter coordinates and coefficient charts. It assumes no torus defined over `F`.
