# Points of the additive group, character values and the open cell

Author: Worker 239.

Module `Langlands.GroupScheme.Reductive.RankOneRootCellRelation`. This is an internal
supporting unit for the proof of `SplitRankOneRootCellStatement`. It sets up notation and
elementary identities for points of `𝔾ₐ`, for values of characters, and for points of an
open cell `xm(Y) t xp(X)`. It proves no theorem from the literature.

## Definitions (namespace `Langlands.GroupScheme.RankOneRootCellRelation`)

Test schemes `Z` and `W` are objects of `Over (Spec k)`, and points are morphisms there.

- `Ga k` is the additive group `VectorGroup.groupScheme (CommRingCat.of k) 1`.
- `gpt x : Z ⟶ (Ga k).X` is the point with coordinate `x ∈ Γ(Z.left, ⊤)`.
- `cu χ t : Γ(Z.left, ⊤)ˣ` is the value `χ(t)` of a character `χ` of a commutative group
  scheme `S` at a point `t : Z ⟶ S.X`, as a unit via `Gm.pointsEquiv`.
- `CellData k` is a structure with fields `G`, `T`, `i : T.toGrp ⟶ G`,
  `xp xm : Ga k ⟶ G`, a character `α` of `T`, and three properties: `hxp` (conjugation by
  points of `T` acts on `xp` through `α`, in the form of clause 1 of
  `SplitRankOneRootCellStatement`), `hxm` (the same for `xm` and `-α`) and `open_cell`
  (`(Dynamic.tripleCellMultiplication xm i xp).left` is an open immersion). It asks for
  nothing else: no reductivity, maximality or root datum.
- For `D : CellData k`: `D.A x = gpt x ≫ xp`, `D.B y = gpt y ≫ xm` and `D.I t = t ≫ i`
  are the points `xp(x)`, `xm(y)` and `t` of `G`. `D.cellMul` is
  `Dynamic.tripleCellMultiplication xm i xp`, `D.cellPt y t x = D.B y * (D.I t * D.A x)` is
  the cell point `xm(y) t xp(x)`, and `D.InCell g` says that `g` factors through
  `D.cellMul`.

## Results

- **Points of `𝔾ₐ`.** `coordinates_gpt`, `eq_gpt` and `gpt_injective`: a point is
  determined by its coordinate. `gpt_add`, `gpt_zero` and `gpt_neg`: `gpt` turns addition
  into the group law. `comp_gpt`: pulling back along `f : W ⟶ Z` applies
  `f.left.appTop` to the coordinate. `weightPointAction_gpt`:
  `VectorGroup.weightPointAction χ Z t (gpt x) = gpt (χ(t) x)`.
- **Character values.** `charValue_eq_cu` (by definition), `cu_mul`, `cu_one`, `cu_inv`,
  `cu_neg` (`(-χ)(t) = χ(t)⁻¹`) and `cu_comp` (naturality in `Z`).
- **Root groups and the torus.** `A_add`, `B_add`, `A_zero`, `B_zero`, `A_neg`, `B_neg`,
  `A_sub`, `I_mul`, `I_one`, `I_inv`, and the pullback rules `comp_A`, `comp_B`,
  `comp_I`. The commutation rules `I_mul_A` (`t xp(x) = xp(α(t) x) t`), `I_mul_B`
  (`t xm(y) = xm(α(t)⁻¹ y) t`), `A_mul_I` and `B_mul_I` restate `hxp` and `hxm`.
- **Cell points.** `lift_cellMul` computes `D.cellMul` on a point.
  `inCell_iff`: `D.InCell g` holds if and only if `g = D.cellPt y t x` for some `y`, `t`,
  `x`. `inCell_cellPt`. `cellPt_inj`: the coordinates of a cell point are unique.
  `one_eq_cellPt`, `A_eq_cellPt`, `I_eq_cellPt`: `1`, `xp(x)` and `t` are cell points.
- **Multiplying cell points.** `B_mul_cellPt`, `I_mul_cellPt`, `cellPt_mul_A`,
  `cellPt_mul_I` give the cell coordinates of `xm(y') Ω`, `s Ω`, `Ω xp(x')` and `Ω s` for a
  cell point `Ω`, and `comp_cellPt` gives its pullback. Correspondingly
  `InCell.B_mul`, `InCell.I_mul`, `InCell.mul_A`, `InCell.mul_I` and `InCell.comp`.
- **Cell membership through points of schemes.** `inCell_of_range_subset`: if the image of
  `g.left` lies in the image of `D.cellMul.left`, then `D.InCell g`.
  `range_subset_of_inCell` is the converse. `InCell.of_comp`: if `f : W ⟶ Z` is surjective
  on underlying points and `D.InCell (f ≫ g)`, then `D.InCell g`.

## The implemented proof

The identities for `gpt` are checked coordinatewise with `VectorGroup.points_ext`. The
identities for `cu` come from `Gm.pointsEquiv` being a natural multiplicative equivalence
and from `evalPoint` being additive in the character. `inCell_iff` writes a factorization
`c` as `lift (gpt y) (lift t (gpt x))`, using `eq_gpt` on the two outer components.
`cellPt_inj` uses that an open immersion is a monomorphism: two cell points with the same
image have the same lift to `𝔾ₐ × T × 𝔾ₐ`, and its three projections give the coordinates.
`inCell_of_range_subset` lifts `g.left` through the open immersion with
`IsOpenImmersion.lift`; the lift is a morphism over `Spec k` because the cell map is.
`InCell.of_comp` combines the two range statements with the surjectivity of `f.left`.

## Provenance

This module is internal and derived; it does not formalize a cited theorem. The cell
`xm(Y) t xp(X)` is the open cell `Ω_a` of Conrad, *Reductive group schemes*, Theorem 4.1.4
(literature `conrad-2014-reductive-group-schemes`), which `SplitRankOneRootCellStatement`
formalizes.

`Ga` and `gpt` abbreviate the existing `RootCell.Ga` and `RootCell.pt` from `SplitRankOneRootCellReduction`.
