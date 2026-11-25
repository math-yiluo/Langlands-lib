# The root cell of `SL₂ × C`

Module `Langlands.GroupScheme.Reductive.SpecialLinearTensorCell`, namespace
`Langlands.GroupScheme.SpecialLinearTensorCell`. This is an internal supporting module. It
was written for the rank-one central cover
(`Langlands.GroupScheme.RankOneCentralCoverStatement`). There, `RootCell.exists_powerIsogeny`
compares the root cell of `SL₂ × C` with a root cell of the reductive group `G`.

Its main result is `isRootCell₀`. For a commutative group scheme `C` over a field `k`,
the group `SL₂ × C` has a root cell in the sense of `RootCell.IsRootCell`, with middle
factor the commutative group scheme `𝔾ₘ × C`. The cell character is `(τ, c) ↦ τ²` and
the cell cocharacter is `s ↦ (s, 1)`; they come from the root and coroot of the diagonal
torus of `SL₂`. These are the standard data of the big cell `U⁻ T U⁺` of `SL₂`, with the
relation `x₊(a) x₋(b) = x₋(b/u) α∨(u) x₊(a/u)` for `u = 1 + ab`. The module states them
for `SL₂ × C` and proves them by explicit `2 × 2` matrix computations. It uses no
classification, root-datum or Borel input.

The construction makes sense for every commutative `C`, but `𝔾ₘ × C` is a torus only for
suitable `C`. For example, if `C` is the constant group of order two, then `𝔾ₘ × C` is
geometrically disconnected, so it is not a torus. The rank-one central cover applies
`isRootCell₀` with `C` a split torus (`RankOneCentralCoverStatement` requires
`IsSplitTorus C.toGrp`). In that case `𝔾ₘ × C` is a split torus, and the cell character
and cocharacter play the role of a root and its coroot. This module proves no torus
property of `𝔾ₘ × C`; it only uses that `C` is commutative.

## Matrix identities (section `Matrices`, any commutative ring `A`)

- `up a`, `lo b` are the transvections `[[1, a], [0, 1]]` and `[[1, 0], [b, 1]]` in
  `SL(2, A)` (`coe_up`, `coe_lo`). `dg s` is `diag(s, s⁻¹)` for a unit `s` (`coe_dg`).
  `wy` is the Weyl matrix `[[0, 1], [-1, 0]]`.
- `coe_torusMatrix_one`, `torusMatrix_eq_dg`: the Library's rank-one diagonal torus matrix
  `SpecialLinear.FinSucc.torusMatrix τ` is `dg (τ ⟨0⟩)`.
- `coe_inv_two`: the inverse of `g ∈ SL(2, A)` is `[[g₁₁, -g₀₁], [-g₁₀, g₀₀]]`.
- `dg_up_dg_inv`, `dg_lo_dg_inv`: `dg s · up a · (dg s)⁻¹ = up (s² a)` and
  `dg s · lo b · (dg s)⁻¹ = lo (s⁻² b)`.
- `up_mul_lo`: if `u = 1 + ab` is a unit, then
  `up a · lo b = lo (u⁻¹ b) · dg u · up (u⁻¹ a)`.
- `up_mul_lo_apply_zero_zero`: the `(0, 0)` entry of `up a · lo b` is `1 + ab`.
- `coe_cell`: `lo m · (dg s · up p) = [[s, s p], [m s, m s p + s⁻¹]]`.
- `cell_injective`: the triple `(m, s, p)` is determined by `lo m · (dg s · up p)`.
- `eq_cell`: if the entry `g₀₀` equals the unit `s`, then
  `g = lo (g₁₀ s⁻¹) · (dg s · up (s⁻¹ g₀₁))`. It uses `det g = 1`.
- `wy_up_wy_inv`: `wy · up a · wy⁻¹ = lo (-a)`. `wy_mul_apply_zero_zero`: the `(0, 0)`
  entry of `wy · g` is `g₁₀`.

## The group scheme `SL₂ × C` (section `GroupScheme`)

Fix a field `k : Type u` and `C : CommGroupScheme (Spec (CommRingCat.of k))`.

- `SL2 k` is `SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)`. `Dt k` is the
  one-dimensional split torus `splitTorus.commGroupScheme _ (ULift (Fin 1))`.
- `G₀ C := SL2 k ⊗ C.toGrp`, the product group scheme `SL₂ × C`. It is a `def`, so that
  instance search finds the group law on its points directly.
- `T₀ C := CommGroupScheme.prod (Dt k) C` is the commutative group scheme `𝔾ₘ × C`, the
  middle factor of the cell. It is a split torus when `C` is a split torus, but not for
  every commutative `C` (see above). The homomorphism `i₀ C : (T₀ C).toGrp ⟶ G₀ C` is
  `SpecialLinear.FinSucc.diagonalTorus 1 ⊗ₘ 𝟙`. When `C` is split, this is the left side
  of the target's torus compatibility.
- `xp₀ C`, `xm₀ C : Ga k ⟶ G₀ C` are `a ↦ (up a, 1)` and `b ↦ (lo b, 1)`. They are built
  from the Library maps `SpecialLinear.BinaryRoot.upperMap` and `lowerMap`.
- `χ₀ C : characterLattice (T₀ C)`, a homomorphism `𝔾ₘ × C ⟶ 𝔾ₘ`, is the cell character
  `prodFst ≫ 2 • proj ⟨0⟩`, that is `(τ, c) ↦ τ²`. `χv₀ C : cocharacterLattice (T₀ C)`, a
  homomorphism `𝔾ₘ ⟶ 𝔾ₘ × C`, is the cell cocharacter `single ⟨0⟩ ≫ prodInl`, that is
  `s ↦ (s, 1)`. They are the root and coroot of the diagonal torus of `SL₂`, composed with
  the first projection and the first inclusion. The names root and coroot for them are
  appropriate only in the torus case described above.
- `ptEquiv C Z` is a group isomorphism. It sends `Z`-points of `G₀ C` to pairs of a
  matrix in `SL(2, Γ(Z, 𝒪))` and a `Z`-point of `C`. It is built from
  `GroupScheme.productPointsEquiv` and `SpecialLinear.pointsEquiv`, and `ptEquiv_apply`
  unfolds it.
- `tc t` is the unit coordinate of a point `t` of `𝔾ₘ × C`.
- `g₀ C` is the upper-left matrix entry, a global function on `G₀ C`. `appTop_g₀` says
  that its value at a point `y` is the `(0, 0)` entry of `(ptEquiv C Z y).1`.
- `cell₀ C : RootCell.Cell (T₀ C) ⟶ (G₀ C).X` is the open-cell map
  `(m, t, p) ↦ xm₀(m) i₀(t) xp₀(p)`, i.e. `Dynamic.tripleCellMultiplication`.

Point formulas: `ptEquiv_i₀` (`t ↦ (dg (tc t), t ≫ snd)`), `ptEquiv_xp₀`, `ptEquiv_xm₀`,
`ptEquiv_coroot` (`χv₀(u)` maps to `(dg u, 1)`), `ptEquiv_lift_cell₀` and `ptEquiv_cell₀`
(`(m, t, p)` maps to `(lo m · (dg (tc t) · up p), t ≫ snd)`). The values of the cell character are
`gm_χ₀`, `charValue_χ₀` (`χ₀(t) = tc t²`) and `charValue_neg_χ₀`. `crd_weightPointAction`
gives the coordinate of a weight action. `i₀_hom`, `xp₀_hom`, `xm₀_hom`, `i₀_fst`,
`i₀_snd`, `one_hom_comp`, `comp_prodFst`, `prodInl_hom_fst`, `prodInl_hom_snd` are
unfolding lemmas.

## The root cell

`isRootCell₀ : RootCell.IsRootCell (i₀ C) (χ₀ C) (χv₀ C) (xp₀ C) (xm₀ C)`. Its five fields
are proved separately.

- `conj_xp₀`, `conj_xm₀`: conjugating `xp₀(a)` by `i₀(t)` gives `xp₀(χ₀(t) a)`, and
  conjugating `xm₀(b)` gives `xm₀(χ₀(t)⁻¹ b)`. Apply `ptEquiv`. The matrix part is
  `dg_up_dg_inv` or `dg_lo_dg_inv`. The `C`-part is `c · 1 · c⁻¹ = 1`.
- `mul_eq₀`: the rank-one relation. If `u = 1 + ab`, `a' = u⁻¹ a` and `b' = u⁻¹ b`, then
  `xp₀(a) xm₀(b) = xm₀(b') i₀(χv₀(u)) xp₀(a')`. Apply `ptEquiv` and use `up_mul_lo` and
  `ptEquiv_coroot`.
- `exists_iff₀`: `xp₀(a) xm₀(b)` lies in the cell if and only if `1 + ab` is a unit. If it
  equals `cell₀(c)`, compare the `(0, 0)` entries (`ptEquiv_cell₀`, `coe_cell`,
  `up_mul_lo_apply_zero_zero`). Then `1 + ab` equals the unit `tc(...)`. Conversely, if
  `u = 1 + ab` is a unit, `mul_eq₀` writes the product as
  `cell₀(u⁻¹ b, χv₀(u), u⁻¹ a)`.
- `mono_cell₀`: `cell₀ C` is a monomorphism. If two cell points have the same image, then
  `cell_injective` gives equal `𝔾ₐ` coordinates and equal unit coordinates `tc`, and the
  `C`-parts agree. The `𝔾ₘ`-parts are then equal by injectivity of
  `splitTorus.pointsEquiv`, because `ULift (Fin 1)` has a single element. So the cell
  points agree (`RootCell.eq_lift`, `RootCell.crd_injective`).
- `isOpenImmersion_cell₀`: `(cell₀ C).left` is an open immersion. This applies
  `UnitLocus.isOpenImmersion_of_unitLocus` with the function `g₀ C`. The entry `g₀`
  pulls back along `cell₀` to the unit `tc`. If `g₀(y)` is a unit `s` at a point `y`, put
  `τ = (s, y ≫ snd)`, a point of `𝔾ₘ × C`. Then `eq_cell` shows that
  `y = cell₀((ptEquiv y)₁₀ s⁻¹, τ, s⁻¹ (ptEquiv y)₀₁)`.

## Provenance

Internal. The definitions are the textbook root groups, diagonal torus, root, coroot and
big cell of `SL₂`. No single source is cited, and none of the statements needs one: each is
an explicit `2 × 2` matrix identity checked in Lean. They are taken on a product with an
arbitrary commutative group scheme `C`, on which the root-group maps are trivial.
The explicit forms (`diagonalTorus 1`, `BinaryRoot.upperMap`, `lowerMap`) are the Library's
existing `SL₂` maps. The cell character `(τ, c) ↦ τ²` and cell cocharacter `s ↦ (s, 1)`
come from the root and coroot of the diagonal torus of `SL₂`. All facts are proved by direct computation here.
