# Kaletha–Prasad §1.1: geodesics, nonpositive curvature, convexity, barycenters and bounded actions

Module `Langlands.Geometry.Metric.KPDefinitions`, namespace `Langlands.Geometry.Metric.KP`.

This module provides the metric-space definitions of Section 1.1 of Kaletha–Prasad over Mathlib
metric spaces (`[MetricSpace X]`). It also proves the comparison laws that connect the
normalized presentations used here to the literal source definitions. It contains no fixed-point
theorem and no building. Lemma 1.1.11, Lemma 1.1.13, Theorem 1.1.15 and Corollary 1.1.19 are
neither proved nor assumed (see "Not proved here" below).

## Sources

- `kaletha-prasad-2023-bruhat-tits-new-approach`: T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A
  New Approach*, Cambridge University Press 2023. PDF SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. Section 1.1 ("Metric
  Spaces") is printed pp. 3–8 = PDF pp. 34–39.
- `kaletha-prasad-2024-corrections`: Kaletha–Prasad, *Corrections and additions to Bruhat–Tits
  theory: a new approach*, version of 1 November 2024. PDF SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. The Section 1.1 bullets
  are on PDF pp. 1–2.

Corrections applied, from corrections PDF p. 1:

- Definition 1.1.12(1): "A subset" becomes "A nonempty subset".
- "In the statement of Lemma 1.1.13 and Remark 1.1.14 replace 'metric space' with 'geodesic
  space'". The book has no Remark 1.1.14. The item numbered 1.1.14 is Definition 1.1.14, and its
  statement begins "Let (X, d) be a non-positively curved metric space". The correction is read
  as applying to that statement, so it becomes "a non-positively curved geodesic space".

The corrections to the proofs of Theorem 1.1.15 and Proposition 1.1.20 (PDF p. 2) change proofs
that are not part of this unit.

## Source map

| Source (KP 2023) | Location | Lean declaration |
| --- | --- | --- |
| Definition 1.1.1(1), bounded subset | printed p. 3 / PDF 34 | Mathlib `Bornology.IsBounded`; comparison `isBounded_iff_subset_ball_pos` |
| Definition 1.1.1(2), joint diameter `diam(A, B)` | printed p. 3 / PDF 34 | `jointDiam` |
| Definition 1.1.1(3), `diam(A) = diam(A, A)` | printed p. 3 / PDF 34 | `jointDiam_self` (equals Mathlib `Metric.ediam`) |
| Curve `c : [0,1] → X` and length (1.1.1) | printed pp. 3–4 / PDF 34–35 | `IsUnitPartition`, `partitionSum`, `curveLength`; curves are `C(I, X)`, Mathlib `Path x y` for curves joining `x, y` |
| Definition 1.1.2(1), rectifiable | printed p. 4 / PDF 35 | `IsRectifiable` |
| Definition 1.1.2(2), restriction `c|[t₁,t₂]`, geodesic | printed p. 4 / PDF 35 | `curveRestrict`, `IsSourceGeodesic` (literal); `IsGeodesicCurve`, `IsGeodesic` (normalized) |
| Remark after 1.1.3: `d(x, y) ≤ ℓ(c)` | printed p. 4 / PDF 35 | `edist_le_curveLength` |
| Definition 1.1.4, geodesic / uniquely geodesic space | printed p. 4 / PDF 35 | `IsGeodesicSpace`, `IsUniquelyGeodesicSpace` |
| Definition 1.1.8, non-positively curved | printed p. 4 / PDF 35 | `IsNPCMidpoint`, `IsNonpositivelyCurved` |
| Remark 1.1.9, parallelogram law | printed p. 5 / PDF 36 | example `isNPCMidpoint_smul_add` |
| Definition 1.1.12(1), convex (corrected: nonempty) | printed p. 5 / PDF 36; corrections p. 1 | `IsSourceConvex` (literal); `IsGeodesicallyConvex` (all-segments); carrier-only `ContainsGeodesics` |
| Definition 1.1.12(2), radius `r(M)` | printed p. 5 / PDF 36 | `radius` |
| Definition 1.1.12(3), barycenter | printed p. 5 / PDF 36 | `IsBarycenter` |
| Definition 1.1.14, closed convex hull (corrected: geodesic space) | printed p. 6 / PDF 37; corrections p. 1 | `closedGeodesicConvexHull` |
| Lemma 1.1.17, one bounded orbit iff all bounded | printed p. 7 / PDF 38 | `hasBoundedAction_iff_forall` (proved) |
| Definition 1.1.18, bounded action | printed p. 7 / PDF 38 | `HasBoundedAction` |

## Definitions

### Curves and length

- `IsUnitPartition t` for `t : Fin (n + 1) → I` means that `t` is strictly increasing with
  `t 0 = 0` and `t (Fin.last n) = 1`. These are the finite sequences `0 = t₀ < t₁ < ⋯ < tₙ = 1`
  of (1.1.1).
- `partitionSum c t = ∑_{i < n} edist (c tᵢ) (c tᵢ₊₁)`.
- `curveLength c` is the supremum of `partitionSum c t` over all `n` and all `t` with
  `IsUnitPartition t`. This is (1.1.1). Its value lies in `ℝ≥0∞ = [0, ∞]`, so the supremum is the
  genuine one and a non-rectifiable curve has length `⊤`. It is defined for every map `I → X`,
  and the source applies it to continuous curves.
- `IsRectifiable c` for `c : C(I, X)` means `curveLength c < ⊤` (Definition 1.1.2(1)).
- `curveRestrict c t₁ t₂ = c ∘ Set.Icc.convexComb t₁ t₂`, that is
  `s ↦ c((1 - s) t₁ + s t₂) = c(t₁ + s (t₂ - t₁))`. This is the source restriction `c|[t₁,t₂]`.
  For a path `γ`, Mathlib's `γ.subpath t₁ t₂` has exactly this underlying function.
- `IsSourceGeodesic c` for `c : C(I, X)` is Definition 1.1.2(2) word for word: `c` is
  rectifiable, and for all `0 < t₁ < t₂ < 1`, `curveLength (curveRestrict c t₁ t₂) =
  edist (c t₁) (c t₂)` and `dist (c t₁) (c t₂) = dist (c 0) (c 1) * |t₁ - t₂|`.

### Normalized geodesics (distance law)

- `IsGeodesicCurve c` for `c : I → X` means `dist (c s) (c t) = dist (c 0) (c 1) * |s - t|`
  for all `s, t ∈ [0,1]`.
- `IsGeodesic γ` for a Mathlib path `γ : Path x y` (so `γ 0 = x`, `γ 1 = y`) means
  `dist (γ s) (γ t) = dist x y * |s - t|` for all `s, t`. This is the geodesic segment joining
  `x` and `y`. Its parameter interval is `[0, 1]`, its endpoints are fixed by the type, and it
  satisfies the constant-speed law.
- `IsGeodesicSpace X` means that for all `x y` there is `γ : Path x y` with `IsGeodesic γ`.
- `IsUniquelyGeodesicSpace X` means that for all `x y` there is exactly one such `γ`
  (`∃! γ : Path x y, IsGeodesic γ`). This is "connected by a geodesic … that geodesic is
  unique" (Definition 1.1.4).

### Nonpositive curvature

- `IsNPCMidpoint x y m` means that for all `z`,
  `2 * dist m z ^ 2 + (1 / 2) * dist x y ^ 2 ≤ dist x z ^ 2 + dist y z ^ 2`.
- `IsNonpositivelyCurved X` means that for all `x y` there is `m` with `IsNPCMidpoint x y m`.
  This is exactly Definition 1.1.8. The predicate includes no completeness, no geodesic existence,
  no uniqueness of geodesics or midpoints, and no convexity, barycenter or fixed-point property.

### Joint diameter, radius and barycenters

- `jointDiam A B = ⨆ a ∈ A, ⨆ b ∈ B, edist a b`, valued in `[0, ∞]`. The source (Definition
  1.1.1) also uses `[0, ∞]`-valued diameters: "diam(A) is finite precisely when A is bounded".
  The source defines `diam(A, B)` only for nonempty `A, B`; for an empty argument this
  supremum is `0`. The source's `diam(x, M)` is `jointDiam {x} M = ⨆ m ∈ M, edist x m`
  (`jointDiam_singleton_left`).
- `radius M = ⨅ x ∈ M, jointDiam {x} M`, valued in `[0, ∞]`. This is
  `r(M) = inf {diam(x, M) | x ∈ M}`: centers range over `M` and the supremum is taken over `M`.
- `IsBarycenter M b` means `b ∈ M ∧ jointDiam {b} M = radius M`.

### Convexity

- `ContainsGeodesics M` is a carrier-only predicate: for `x, y ∈ M` and every geodesic segment
  `γ : Path x y`, `range γ ⊆ M`. The empty set satisfies it (`containsGeodesics_empty`). It is
  **not** called convex.
- `IsGeodesicallyConvex M` means `M.Nonempty ∧ ContainsGeodesics M`. This is the corrected
  Definition 1.1.12(1) in all-segments form, usable in any metric space.
- `uniqueGeodesic hX x y` is the geodesic chosen from `hX : IsUniquelyGeodesicSpace X`, and
  `eq_uniqueGeodesic` shows that every geodesic from `x` to `y` equals it.
- `IsSourceConvex hX M` is the literal corrected Definition 1.1.12(1) over a uniquely geodesic
  space: `M` is nonempty, and for `x, y ∈ M` the image of the unique geodesic joining `x` and
  `y` lies in `M`.

### Closed convex hull

- `closedGeodesicConvexHull M` is the intersection of all `C` with `IsClosed C`,
  `IsBounded C`, `IsGeodesicallyConvex C` and `M ⊆ C` (Definition 1.1.14).

  The corrected source discussion has these ambient conditions: `X` is a **non-positively curved
  geodesic space** (`IsNonpositivelyCurved X` and `IsGeodesicSpace X`), and `M` is
  **nonempty and bounded**. In that situation the source uses Lemma 1.1.13 to produce one closed
  bounded convex set containing `M`. The Lean intersection is defined without hypotheses, and
  it is `univ` if no such set exists. The name avoids Mathlib's root-level `closedConvexHull`
  for vector spaces.

### Bounded actions

- `HasBoundedAction X A` for `[SMul G X]` and `A : Set G` means that there is `x : X` such that
  `(fun g => g • x) '' A` is bounded. This is Definition 1.1.18 through condition (2) of Lemma
  1.1.17. The source's "set A of isometries" is the set of maps `x ↦ g • x` for `g ∈ A`. It is
  a set of isometries when `[IsIsometricSMul G X]` holds, and the source correspondence uses
  that hypothesis.
- The scoped instances `isometryEquivMulAction` and `isometryEquivIsIsometricSMul` (active after
  `open Langlands.Geometry.Metric.KP`) let `G = X ≃ᵢ X` act on `X` by `f • x = f x`
  (`isometryEquiv_smul_def`). With them, a literal set of isometries `A : Set (X ≃ᵢ X)` can be
  used, and `hasBoundedAction_isometryEquiv_iff` restates the definition for such `A`. Mathlib
  has the group `X ≃ᵢ X` but no action of it on `X`. These instances are scoped so that no
  global instance is added.
- Fixed points, stabilizers and isometries are not redefined. Later statements should use
  Mathlib's `MulAction.fixedPoints`, `MulAction.stabilizer`, `Isometry` and `IsIsometricSMul`.

## Derived choices and proved equivalences

1. **Distance law versus source length.** The working notion `IsGeodesic` is the distance law.
   The following results prove that it matches the source rectifiability/length definition:
   - `partitionSum_eq_of_isGeodesicCurve`: for a curve satisfying the distance law, every
     monotone sum telescopes to `ofReal (dist (c 0) (c 1) * (tₙ - t₀))`. In particular, every
     finite ordered partition sum of `[0, 1]` equals the endpoint distance.
   - `curveLength_eq_of_isGeodesicCurve`: the length (1.1.1) of such a curve is
     `edist (c 0) (c 1)`. The lower bound comes from `edist_le_curveLength`.
   - `IsGeodesicCurve.curveRestrict` and `curveLength_curveRestrict_of_isGeodesicCurve`: each
     restriction `c|[t₁,t₂]` again satisfies the distance law, with constant
     `dist (c t₁) (c t₂)`, and has length `edist (c t₁) (c t₂)`.
   - `isSourceGeodesic_iff`: `IsSourceGeodesic c ↔ IsGeodesicCurve c` for every
     `c : C(I, X)`. In the forward direction, the interior identities extend to all of
     `[0, 1]²` by continuity and density (`dense_Ioo_zero_one`).
   - `isGeodesic_iff_isGeodesicCurve` and `isGeodesic_iff_isSourceGeodesic`: for a path, the
     distance law is exactly being a Definition 1.1.2 geodesic.
   - `isGeodesicSpace_iff_source` and `isUniquelyGeodesicSpace_iff_source`: the space
     predicates are the same whether they quantify over distance-law segments or over literal
     Definition 1.1.2 geodesics.
2. **Convexity.** `isSourceConvex_iff hX M : IsSourceConvex hX M ↔ IsGeodesicallyConvex M`
   over a uniquely geodesic space. In a space that is not uniquely geodesic, the source does not
   define convexity. `IsGeodesicallyConvex` asks for all segments there.
3. **Extended values for radius and barycenter.** No totalized real supremum is used:
   - `jointDiam_singleton_ne_top_iff`: `diam(x, M) ≠ ⊤ ↔ IsBounded M`.
   - `radius_ne_top_iff` (for nonempty `M`): `radius M ≠ ⊤ ↔ IsBounded M`.
   - `radius_empty`: the radius of `∅` is `⊤`.
   - `radius_eq_top_of_not_isBounded`: the radius of an unbounded set is `⊤`.
   - Under explicit hypotheses `M.Nonempty` and `IsBounded M`, the real readings are the genuine
     order-theoretic bounds. `isLUB_toReal_jointDiam_singleton` says that
     `(jointDiam {x} M).toReal` is the least upper bound of `{d(x, m) | m ∈ M}`.
     `isGLB_toReal_radius` says that `(radius M).toReal` is the greatest lower bound of
     `{diam(x, M) | x ∈ M}`. `isBarycenter_iff_toReal` reads the barycenter condition in real
     numbers for bounded `M`.
   - `isBarycenter_of_not_isBounded` records the degenerate case honestly. For an unbounded `M`,
     both sides are `⊤`, so every point of `M` is a barycenter. The source states its barycenter
     theorem (1.1.15) only for bounded sets.
   - The source defines radius and barycenter for convex `M` in a uniquely geodesic space. The
     formulas do not use convexity, so the Lean definitions accept every set. Later statements
     add the convexity and ambient hypotheses.
4. **Boundedness.** Mathlib `IsBounded` is used throughout. `isBounded_iff_subset_ball_pos`
   shows that it agrees with Definition 1.1.1(1) (`A ⊆ B(x, r)` for some `x` and `r > 0`) in a
   nonempty space. The two differ only in the empty space, where the source has no bounded sets.
5. **Bounded action on the empty space.** Lemma 1.1.17 assumes `X` nonempty. On an empty `X`,
   `HasBoundedAction` (some bounded orbit) is false, while "every orbit is bounded" is vacuously
   true. `hasBoundedAction_iff_forall` proves the equivalence for isometric actions on nonempty
   `X`. It is the intrinsic Lemma 1.1.17, proved with the source's triangle-inequality argument.

## Intrinsic laws proved

- Segments: `isGeodesic_refl` (constant, zero-length segments), `IsGeodesic.eq_refl` (a geodesic
  from `x` to `x` is constant), `IsGeodesic.symm` (reversal), `IsGeodesic.subpath` (restriction),
  `IsGeodesic.dist_source` (`d(x, γ t) = t d(x, y)`), `IsGeodesic.dist_target`
  (`d(γ t, y) = (1 - t) d(x, y)`), `IsGeodesic.curveLength_eq` and
  `IsGeodesic.curveLength_subpath`.
- Spaces: `IsUniquelyGeodesicSpace.isGeodesicSpace` and `isUniquelyGeodesicSpace_iff`
  (existence plus uniqueness).
- Curvature: `IsNPCMidpoint.dist_left_le`, `dist_right_le`, `dist_left` and `dist_right`. A point
  satisfying the Definition 1.1.8 inequality for `x, y` (take `z = x` and `z = y`) is a metric
  midpoint: `d(x, m) = d(y, m) = d(x, y)/2`. This does not identify it with a geodesic midpoint
  and does not prove its uniqueness. Those are part of Lemma 1.1.11.
- Convexity: `containsGeodesics_empty`, `containsGeodesics_univ`, `ContainsGeodesics.sInter`,
  `ContainsGeodesics.inter`, `isGeodesicallyConvex_univ`, `isGeodesicallyConvex_singleton` and
  `IsGeodesicallyConvex.apply_mem`.
- Hull: `subset_closedGeodesicConvexHull`, `isClosed_closedGeodesicConvexHull`,
  `closedGeodesicConvexHull_subset` (minimality), `containsGeodesics_closedGeodesicConvexHull`,
  `isGeodesicallyConvex_closedGeodesicConvexHull` (for nonempty `M`) and
  `isBounded_closedGeodesicConvexHull`. Boundedness holds *given* one closed bounded convex set
  containing `M`. The existence of such a set in an NPC geodesic space is Lemma 1.1.13, which is
  not proved here.
- Radius: `radius_le_jointDiam_singleton` and `edist_le_jointDiam_singleton`.
- Helpers: `sum_succ_sub_castSucc` (a telescoping sum over `Fin`) and `dense_Ioo_zero_one`.

## Examples and regressions

- `isGeodesic_segment` and `isGeodesicSpace_of_normedSpace`: in a real normed space, Mathlib's
  `Path.segment x y` (`t ↦ lineMap x y t`) is a geodesic segment, so the space is geodesic.
- `IsGeodesic.eq_segment` and `isUniquelyGeodesicSpace_of_strictConvexSpace`: in a strictly
  convex real normed space, every geodesic segment is the straight one. This uses Mathlib's
  `dist_add_dist_eq_iff`, so the space is uniquely geodesic.
- `isNPCMidpoint_smul_add` and `isNonpositivelyCurved_of_innerProductSpace`: in a real inner
  product space, `(1/2)(x + y)` satisfies Definition 1.1.8 with equality, by the parallelogram
  law (Remark 1.1.9).
- `real_isGeodesicSpace_isUniquelyGeodesicSpace_isNonpositivelyCurved`: the real line is
  geodesic, uniquely geodesic and non-positively curved.
- Regression for the correction of Definition 1.1.12(1): `not_isGeodesicallyConvex_empty` and
  `not_isSourceConvex_empty` (the empty set is not convex), against
  `containsGeodesics_empty`.

These are tests of the definitions, not the intended building instance.

## Not proved here (later statements)

The following source results are **not** proved, stated or assumed in this module, and no
definition contains them as a field:

- Remark 1.1.3 (restrictions of rectifiable curves are rectifiable) and Fact 1.1.6.
- Remark 1.1.10 and **Lemma 1.1.11**: a non-positively curved geodesic space is uniquely geodesic,
  and the geodesic midpoint is the unique point satisfying the Definition 1.1.8 inequality.
- **Lemma 1.1.13** (corrected: in a non-positively curved *geodesic* space closed balls are
  convex). Consequently the source's claim that the closed convex hull is closed, bounded and
  convex in that setting is also unproved. Only the intrinsic hull laws above are proved.
- **Theorem 1.1.15**: existence and uniqueness of barycenters of nonempty bounded closed convex
  sets in complete NPC geodesic spaces, their isometry invariance, and the Bruhat–Tits fixed point
  lemma.
- **Corollary 1.1.19**: a group of isometries with bounded action on a nonempty complete NPC space
  fixes a point.
- Proposition 1.1.20 (nearest-point projection).

Completeness (`CompleteSpace X`) is never part of these predicates. Later statements should
state it separately, together with `IsNonpositivelyCurved X` and `IsGeodesicSpace X`.
