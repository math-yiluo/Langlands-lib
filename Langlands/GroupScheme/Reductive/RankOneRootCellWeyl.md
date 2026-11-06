# The Weyl point and the rank-one relation over algebraically closed points

Author: Worker 239.

Module `Langlands.GroupScheme.Reductive.RankOneRootCellWeyl`. This is an internal
supporting unit for the proof of `SplitRankOneRootCellStatement`. From cell data
(`CellData`, module `RankOneRootCellRelation`) and a `k`-point `n` that normalizes the
torus through the reflection of `α`, it derives clauses 4 and 5 of that statement over test
schemes whose ring of global sections behaves like an algebraically closed field. The root
group `xm` appears rescaled by a unit `β` of `k`; the final module absorbs `β` into `xm`.

## Definitions (namespace `Langlands.GroupScheme.RankOneRootCellRelation`)

- `SqField R`: every element of `R` is zero or a unit, every unit is the square of a unit,
  and some unit has fourth power different from `1`.
- `base k` is `Spec k` as an object of `Over (Spec k)`, and `toBase Z : Z ⟶ base k` is the
  structure morphism.
- `WeylData k` extends `CellData k` by a cocharacter `h` of `T` with
  `pair : ⟨α, h⟩ = 2`, a `k`-point `n : base k ⟶ G.X`, the property
  `hn : IsNormalizingPoint i n (latticeReflectionIso α h pair)` (conjugation by `n` acts on
  `T` through the reflection `t ↦ t · h(α(t))⁻¹`), the property `hn2` that `n * n` is a
  `k`-point of `T`, and `irreducible : IrreducibleSpace G.X.left`.
- For `D : WeylData k`: `D.tH c` and `D.H c` are the points `h(c)` of `T` and of `G` for a
  unit `c`; `D.N Z` is the constant point `n` over `Z`; `D.rho : G.X ⟶ G.X` is right
  multiplication by `n`. `D.cβ`, `D.ct` and `D.cδ` are chosen cell coordinates with
  `xp(1) n = xm(β) γ xp(δ)` over `base k` (`A_one_mul_N_base`), written `β`, `γ`, `δ`
  below, and `λ = α(γ)`. `pb Z x` pulls `x ∈ Γ(Spec k, ⊤)` back to `Z`.

## Results

- `sqField_of_isAlgClosed`, `SqField.of_ringEquiv` and `sqField_Γ_Spec`: for an
  algebraically closed field `K`, the global sections of `Spec K` satisfy `SqField`.
- `field_base` (every global section of `Spec k` is zero or a unit),
  `surjective_toBase_left`, `toBase_eq` and `comp_toBase`.
- `CellData.eq_zero_of_A_mul_B`: if `xp(x) xm(y) = xm(y') t`, then `x = 0`. Also
  `cellPt_zero_right`, `I_mul_A_eq_cellPt` and `I_mul_B'`.
- `hh` (`h ≫ α = 2`), `tH_mul`, `tH_one`, `tH_inv`, `H_mul`, `H_inv`, `comp_tH`,
  `comp_N`, `cu_tH` (`α(h(c)) = c²`).
- `N_mul_I` (conjugation by `n` is the reflection on `T`), `tH_comp_reflection` and
  `N_mul_H` (`n h(c) n⁻¹ = h(c)⁻¹`), with the variants `N_mul_H'`, `H_mul_N`,
  `inv_H_mul_N`, and `I_mul_A'`.
- `A_mul_N` (**equivariance**): `xp(c² x) n = h(c) xp(x) n h(c)`.
- `not_inCell_N`: over `Z` with a unit `c` of `Γ(Z.left, ⊤)` such that `c⁴ ≠ 1`, the point
  `n` is not in the open cell. `not_inCell_N_base`: the same over `base k`.
- `inCell_A_one_mul_N_of_sqField` and `inCell_A_one_mul_N`: `xp(1) n` is in the open cell
  over `base k`. `exists_A_one_mul_N`, `A_one_mul_N_base`, and `A_one_mul_N` (pulled back to
  any `Z`).
- `A_sq_mul_N`: `xp(c²) n = xm(c⁻² β) · h(c) γ h(c) · xp(c⁻² δ)` over any `Z`.
  `N_mul_N`: `n · n` is a point of `T` over any `Z`. `inCell_A`.
- `cβ_isUnit` and `cδ_isUnit`: `β` and `δ` are units of `k`.
- `cu_ct_mul_cδ` (via `cu_mul_eq_neg_one_aux`): `λ δ = -1` over every `Z` on which `δ` is
  the square of a unit.
- `A_sub_mul_B_aux`, and **`rel_of_sqField`**: if `SqField Γ(Z.left, ⊤)` and
  `u = 1 + XY` is a unit, then `xp(X) xm(β Y) = xm(β u⁻¹ Y) · h(u) · xp(u⁻¹ X)`.
- **`not_inCell_of_sqField`**: if `SqField Γ(Z.left, ⊤)` and `1 + XY = 0`, then
  `xp(X) xm(β Y)` is not in the open cell.

## The implemented proof

1. **`n` is not in the cell.** If `n = xm(y) t xp(x)`, conjugate by `h(c)`. By `H_mul_N`,
   `h(c) n h(c)⁻¹ = h(c)² n`. Computing both sides in cell coordinates and comparing torus
   components (`cellPt_inj`) gives `h(c)² = 1`, so `c⁴ = α(h(c))² = 1`.
2. **`xp(1) n` is in the cell.** `G.X.left` is irreducible. The image `Ω` of the cell map is
   open and contains `1`, and its preimage under `rho` is open and contains `n⁻¹`. So the
   two meet at some point `u`. Let `g` be the geometric point
   `Spec (AlgebraicClosure κ(u)) → G` at `u`. Then `g` and `g n` lie in the cell
   (`inCell_of_range_subset`). Over this point, `g = xm(y) t xp(x)`, so
   `xp(x) n = t⁻¹ xm(-y) g n` is in the cell. If `x = 0` this contradicts step 1. Otherwise
   `x = c²` for a unit `c`, and `xp(1) n = h(c)⁻¹ xp(x) n h(c)⁻¹` is in the cell by
   `A_mul_N`. Finally `InCell.of_comp` descends from the geometric point to `base k`, since
   `Spec k` has one point.
3. **`β` is a unit.** Otherwise `β = 0` and `n = xp(-1) γ xp(δ) = γ xp(δ - λ⁻¹)` is in the
   cell, which contradicts `not_inCell_N_base`.
4. **`δ` is a unit.** Otherwise, over `AlgebraicClosure k` choose a unit `c` with
   `c⁴ ≠ 1`. Then `xp(1) n` and `xp(c²) n` both lie in `xm(𝔾ₐ) T` by `A_sq_mul_N`. Dividing,
   `xp(1 - c²) xm(·)` lies in `xm(𝔾ₐ) T` (`eq_zero_of_two`), so `1 - c² = 0` by
   `eq_zero_of_A_mul_B`, a contradiction.
5. **`λ δ = -1`.** Let `δ = d²` on `Z`. Then `n = xp(-1) xm(β) γ xp(δ)`, and by
   `A_sq_mul_N` with `c = d`, `n = xp(-δ) xm(δ⁻¹ β) γ' xp(1)`. Multiplying,
   `n² = xp(-1) · xm(β + λ⁻¹ δ⁻¹ β) γ γ' xp(1)`. Since `n² = z` lies in `T`, also
   `xp(1) z = z xp(λ_z⁻¹)` is a cell point with `xm`-coordinate `0`. By `cellPt_inj`,
   `β (1 + λ⁻¹ δ⁻¹) = 0`; as `β` is a unit, `λ δ = -1` (a `linear_combination`).
6. **The relation.** Let `SqField Γ(Z.left, ⊤)` and `u = 1 + XY`. If `Y = 0` then `u = 1`
   and the claim is `A_eq_cellPt`. Otherwise `Y = w` is a unit; choose units `c'` and `c`
   with `c'² = w⁻¹` and `c² = u w⁻¹`, so `X = c² - c'²` and `β w = c'⁻² β`. With
   `r = c²` and `s = c'²`, `A_sub_mul_B_aux` combines the formulas of `A_sq_mul_N` for `r`
   and `s`: `xp(r - s) xm(s⁻¹ β)` is the cell point with coordinates `r⁻¹ β`, `γ_r γ_s⁻¹`
   and `α(γ_s)(r⁻¹ δ - s⁻¹ δ)`, where `γ_r = h(c) γ h(c)` and `γ_s = h(c') γ h(c')`. Then
   `r⁻¹ β = β u⁻¹ Y`, `γ_r γ_s⁻¹ = h(c² c'⁻²) = h(u)`, and, using `λ δ = -1` from step 5
   (`δ` is a square because `SqField` holds), `α(γ_s)(r⁻¹ δ - s⁻¹ δ) = u⁻¹ X`. The last two
   identities are `ring` and `linear_combination` computations.
7. **Outside the cell.** Let `1 + XY = 0`. If `Y = 0`, then `1 = 0` in `Γ(Z.left, ⊤)`,
   which contradicts the unit with `c⁴ ≠ 1`. Otherwise `Y = w` is a unit; choose `c` with
   `c² = w⁻¹`. Then `X = α(h(c)) · (-1)` and `β w = α(h(c))⁻¹ β`, so
   `xp(X) xm(β Y) = h(c) xp(-1) xm(β) h(c)⁻¹`. If it were in the cell, so would be
   `xp(-1) xm(β)` and hence `n = xp(-1) xm(β) γ xp(δ)`, which contradicts step 1.

## Provenance

This module is internal and derived. Its results are clauses 4 and 5 of
`SplitRankOneRootCellStatement`, which formalizes Conrad, *Reductive group schemes*,
Theorem 4.2.6 (literature `conrad-2014-reductive-group-schemes`), over algebraically closed
points and for a rescaled `xm`. The route is not Conrad's, who works in `PGL₂` after
dividing by the center. It uses only the Weyl point `n`, the identity `n² ∈ T`, the
equivariance `xp(c² x) n = h(c) xp(x) n h(c)`, and square roots of units. For `SL₂` and
the standard Weyl element `n = [[0, 1], [-1, 0]]` one finds `β = 1`, `γ = -1`, `δ = -1`
and `λ = 1`, matching the calculation of Conrad, Example 4.2.5.
