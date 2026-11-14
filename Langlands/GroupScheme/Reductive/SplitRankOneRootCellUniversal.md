# The cell criterion and the rank-one relation from algebraically closed points

Author: Worker 1388.

Module `Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal`. This is an
internal supporting unit for the proof of `SplitRankOneRootCellStatement`. It handles
clauses 4 and 5 of that statement: the cell criterion and the rank-one relation. It shows
that it is enough to prove them over `Spec K` for algebraically closed fields `K` over
`k`. It does not use the root datum, reductivity or the conjugation clauses; it holds
for any `T`, `G`, `i : T.toGrp ⟶ G`, cocharacter `χv` and morphisms `xp xm : 𝔾ₐ ⟶ G`.
Where noted, it assumes `[IsSeparated G.X.hom]`. This holds when `G` is affine over `k`,
for example when `G` is connected reductive.

## Definitions (namespace `Langlands.GroupScheme.RootCell`)

`Ga k`, `crd` and `pt` are those of `SplitRankOneRootCellReduction`.

- `RelationAt i χv xp xm Z a b a' b' u` is the equation
  `xp(a) xm(b) = xm(b') χv(u) xp(a')` of points `Z ⟶ G.X`, written exactly as in clause 5
  of `SplitRankOneRootCellStatement`, for `χv` in place of `P.coroot r`.
- `RelationOver i χv xp xm Z` is clause 5 over the single test scheme `Z`: for all
  points `a, b, a', b'` of `𝔾ₐ` over `Z` and every unit `u` with `u = 1 + crd a · crd b`,
  `crd a' = u⁻¹ crd a` and `crd b' = u⁻¹ crd b`, `RelationAt … Z a b a' b' u` holds.
- `InCell i xp xm a b` says that `xp(a) xm(b)` factors through
  `Dynamic.tripleCellMultiplication xm i xp`. This is the left side of clause 4.
- `algClosedPt X x : Spec (AlgebraicClosure κ(x)) ⟶ X` is `Spec` of the inclusion
  `κ(x) → AlgebraicClosure κ(x)`, followed by `X.fromSpecResidueField x`. It maps every
  point to `x` (`algClosedPt_apply`).
- In the namespace `Universal`: `plane k` is `𝔾ₐ²` with coordinates `cX k` and `cY k`;
  `openU k` is its basic open subset `1 + XY ≠ 0`; `overU k` is that open subscheme as a
  scheme over `k`; `univX k` and `univY k` are the restricted coordinates; `univUnit k` is
  the unit `1 + XY` on `overU k`.

## Results

- `crd_injective`, `crd_comp`, `coe_units_map`, `coe_units_map_inv`,
  `symm_pointsEquiv_comp`: points of `𝔾ₐ` are determined by their coordinate, and
  coordinates and units pull back along `w : Z' ⟶ Z` through `w.left.appTop`.
- `relationAt_comp_iff`, `RelationAt.comp`, `InCell.comp`: the relation and cell membership
  pull back along `w : Z' ⟶ Z`.
- `RelationOver.apply_comp`: if `RelationOver … Z'` holds, then for `w : Z' ⟶ Z` and data
  over `Z` satisfying the hypotheses of clause 5, the relation holds for the pulled-back
  data over `Z'`.
- `RelationAt.of_comp` (assumes `[IsSeparated G.X.hom]`): if `Z.left` is reduced and
  `w.left` is dominant, then the relation for the pulled-back data over `Z'` implies the
  relation over `Z`.
- `algClosedPt_preimage_eq_bot`, and an instance: `algClosedPt X (genericPoint X)` is
  dominant when `X` is irreducible.
- `Universal.one_add_ne_zero`, `Universal.nonempty_openU`, the instance
  `IsIntegral (overU k).left`, and `Universal.isUnit_univ`.
- `relationAt_univ` (assumes `[IsSeparated G.X.hom]`): if `RelationOver … (Over.mk f)`
  holds for every algebraically closed field `K` and every `f : Spec K ⟶ Spec k`, then the
  relation holds at the universal point of `overU k`, that is, for
  `a = pt (univX k)`, `b = pt (univY k)`, `u = univUnit k`, `a' = pt (u⁻¹ · univX k)` and
  `b' = pt (u⁻¹ · univY k)`.
- `relationOver_of_isAlgClosed` (assumes `[IsSeparated G.X.hom]`): under the same
  hypothesis, `RelationOver i χv xp xm Z` holds for every `Z`.
- `inCell_of_relationOver`: if `RelationOver … Z` holds and `1 + crd a · crd b` is a unit,
  then `InCell … a b`.
- `isUnit_of_inCell`: suppose that for every algebraically closed `K` over `k` and all
  points `a, b` over `Spec K` with `1 + crd a · crd b = 0`, `InCell … a b` fails. Then over
  every `Z`, `InCell … a b` implies that `1 + crd a · crd b` is a unit.
- `inCell_iff_and_relationOver` (assumes `[IsSeparated G.X.hom]`): from the relation over
  all algebraically closed fields (`hrel`) and the failure of cell membership over them
  when `1 + XY = 0` (`hcell`), it proves clause 4,
  `InCell … a b ↔ IsUnit (1 + crd a · crd b)` for all `Z, a, b`, and clause 5,
  `RelationOver … Z` for all `Z`.

## The implemented proof

1. **The universal point.** `plane k` is `Spec k[X, Y]`, which is integral. The element
   `1 + XY` is nonzero (its constant coefficient is `1`), so `openU k` is a nonempty open
   subscheme of an integral scheme, and `overU k` is integral. `1 + XY` restricts to a unit
   on `openU k`.
2. **`relationAt_univ`.** Let `g = algClosedPt (overU k).left η` for the generic point `η`.
   It is dominant: its image is `{η}`, whose closure is everything. Apply the hypothesis to
   `K = AlgebraicClosure κ(η)` and `f = g ≫ (overU k).hom`. `RelationOver.apply_comp` gives
   the relation for the universal data pulled back along `w = Over.homMk g`. The side
   conditions hold by `crd_pt` and `IsUnit.unit_spec`. `RelationAt.of_comp` then descends
   it to `overU k`. Its proof applies Mathlib's `ext_of_isDominant_of_isSeparated` to the
   two sides of the relation. These are morphisms from the reduced scheme `(overU k).left`
   to `G.X.left` over `Spec k`, and they agree after composition with the dominant `g`.
3. **`relationOver_of_isAlgClosed`.** Given `Z`, `a`, `b`, `u`, `a'` and `b'` as in
   clause 5, let `v : Z ⟶ plane k` be the point with coordinates `(crd a, crd b)`. The
   pullback of `1 + XY` along `v` is `u`, a unit, so the preimage of `openU k` is all of
   `Z`. Hence `v` factors as `φ : Z ⟶ overU k` (`IsOpenImmersion.lift`). Pulling back
   along `φ`, the universal data become `a`, `b`, `u`, `a'` and `b'` (by `crd_injective`
   and the hypotheses on `a'` and `b'`). So the claim is `RelationAt.comp φ` of
   `relationAt_univ`.
4. **`inCell_of_relationOver`.** The relation writes `xp(a) xm(b)` as
   `xm(b') χv(u) xp(a')`, which is the image of the cell point `(b', χv(u), a')` under
   `Dynamic.tripleCellMultiplication` (`Dynamic.lift_tripleCellMultiplication`).
5. **`isUnit_of_inCell`.** Suppose `1 + crd a · crd b` is not a unit. Then its basic open
   subset is not everything, so it vanishes at some point `x` of `Z.left`. Let
   `g = algClosedPt Z.left x` and `w = Over.homMk g`. The preimage under `g` of the basic
   open subset is empty, because `g` maps everything to `x`. The spectrum of a field is
   reduced, so the pullback of `1 + crd a · crd b` along `g` is zero. By `crd_comp` this
   pullback is `1 + crd (w ≫ a) · crd (w ≫ b)`. `InCell.comp w` gives cell membership over
   `Spec (AlgebraicClosure κ(x))`, which contradicts the hypothesis.
6. **`inCell_iff_and_relationOver`.** Clause 5 is step 3. In clause 4, `→` is step 5, and
   `←` is step 4 applied to step 3.

## Provenance

This module is internal and derived; it does not formalize a cited theorem. The
reduction to algebraically closed fields follows the standard pattern: test an identity
of morphisms out of a reduced scheme on a dominant family of points, and detect units at
residue fields. Worker 239 suggested the shape of the hypotheses (`hrel` and `hcell` over
algebraically closed `K`). Their field-level argument for the rank-one relation needs
square roots.

`algClosedPt` abbreviates the existing `GroupScheme.geometricPoint` from `Reductive.Basic`.

The coordinate helper `RootCell.crd_injective` is imported from
`SplitRankOneRootCellReduction`; its original statement and proof are unchanged.
