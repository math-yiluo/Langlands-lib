# Opposite factor pairs of linked root parametrizations of arbitrary roots

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.LinkedRootOppositePairs`.

Let `k` be a field, `G` an affine group scheme over `Spec k`, and `p : SplitPinning G` a
split pinning. `U_r` denotes the rational points
`(RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier (Over.mk (𝟙 _))` of the
intrinsic root subgroup of a root index `r : p.rootIndex`. The root need not be simple. The
published module `Rational.NegativeRootPartner` computes opposite factor pairs for
normalized simple-root maps. This module does the same for linked parametrizations of
arbitrary roots. It also compares the opposite-pair products of different points.

## Linked parametrizations (namespace `LinkedRootParametrization`)

Fix `X : LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r)`.
`X.xpPoint`, `X.xmPoint` and `cocharacterPoint` are the rational points of the published
module `Reductive.LinkedRootRationalRelation`.

- `pairing_root_coroot'`: `⟨root r, coroot r⟩ = 2`. This follows from `p.isRootDatum.1` and
  `RootPairing.root_coroot_two`.
- `pinnedData` (definition): the rank-one data `X.rankOneData pairing_root_coroot'`. Its maps
  are `xp = X.xpPoint`, `xm = X.xmPoint` and `h = cocharacterPoint p.inclusion (coroot r)`.
- `xpPoint_mem c`, `xmPoint_mem c`: `x₊(c) ∈ U_r` and `x₋(c) ∈ U_{-r}`, from the
  representability fields of `X`.
- `xpPoint_ne_one hc`: `x₊(c) ≠ 1` for `c ≠ 0`. Use `x₊(0) = 1`, cancel the monomorphism
  `X.positive`, then use injectivity of the additive-group points (`gpt_injective`) and of
  `secMap`.
- `isOppositeFactorPair_xpPoint_one`: `(x₋(-1), x₋(-1))` is an opposite factor pair of
  `x₊(1)` for the root `r`. This is the published `isOppositeFactorPair_weylPoint` (module
  `Reductive.LocalWeylNormalizationField`), applied with the published
  `splitPinnedOppositeFactorPairs`.
- `triple_eq c`: for a unit `c`,
  `x₋(-c⁻¹) x₊(c) x₋(-c⁻¹) = r^∨(c) · (x₋(-1) x₊(1) x₋(-1))`. This is `w_eq_h_mul_w_one`
  for `pinnedData`.
- `isOppositeFactorPair_xpPoint c`: `(x₋(-c⁻¹), x₋(-c⁻¹))` is an opposite factor pair of
  `x₊(c)`. By `triple_eq`, the product is a coroot point times the normalizing element at
  `c = 1`. Coroot points normalize the torus (`cocharacterPoint_mem_normalizerPoints`).
- `exists_xpPoint_eq hg`: every `g ∈ U_r` equals `x₊(c)` for some `c : k`. Apply the
  published `LocalSplitCell.exists_rootPoint_eq` to the character `-root r`, with
  `- -root r = root r`. Then transport the global section through `Scheme.ΓSpecIso`.
- `eq_of_isOppositeFactorPair c hq`: every opposite factor pair of `x₊(c)`, `c` a unit,
  equals `(x₋(-c⁻¹), x₋(-c⁻¹))`. This is the published uniqueness
  `RelativeRoot.IsOppositeFactorPair.eq`.
- `exists_oppositeProduct_eq hy hy1 hq`: for `y ∈ U_r` with `y ≠ 1`, and any opposite factor
  pair `q` of `y`, there is a unit `c` with
  `q.1 * y * q.2 = r^∨(c) · (x₋(-1) x₊(1) x₋(-1))`. Write `y = x₊(c)` with `c ≠ 0`. Then use
  `eq_of_isOppositeFactorPair` and `triple_eq`.

## Products of opposite-pair products (namespace `SplitPinning`)

- `oppositeProduct_mul_mem_range p r hy hy1 hy' hy'1 hq hq'`. Let `y, y' ∈ U_r` both be
  nontrivial, with opposite factor pairs `q` and `q'`. Then
  `(q.1 y q.2) (q'.1 y' q'.2)` lies in the range of
  `cocharacterPoint p.inclusion (coroot r)`. Use the chosen linked parametrization
  `p.linkedRootParametrization r` (published existence `nonempty_linkedRootParametrization`).
  Apply `exists_oppositeProduct_eq` twice. The identity `h_mul_w_mul_h_mul_w` of module
  `Algebra.RankOneRelationWeyl` then gives the value `r^∨(-(c c'⁻¹))`.

## Arbitrary root parametrizations (namespace `SplitPinning.RootParametrization`)

Here `x : p.RootParametrization r` is a root parametrization of the published module
`Rational.SteinbergModifiedRootProduct`, for any root index `r`. An example is the
Galois-compatible merged-root map of `Rational.MergedRootGaloisData`.

- `exists_linked`: there is a linked parametrization `X` of `±r` with `X.positive = x.hom`.
  The proof repeats the published `NormalizedRootParametrization.exists_linked`. Choose any
  linked `X₀`. The published `exists_eq_scaleHom_comp` (applied with `X₀.positive` first and
  `x.hom` second) gives `X₀.positive = scaleHom l ≫ x.hom` with `l ≠ 0`, i.e.
  `X₀.positive(t) = x(l t)`. Take `scaleHom l ≫ X₀.negative` as the negative map, i.e.
  `t ↦ X₀.negative(l t)`. Thus, relative to `X₀`, the positive map is rescaled by `l⁻¹` and
  the negative map by `l`; these reciprocal rescalings keep the coroot `r^∨` and the
  open-cell relation (`u = 1 + (l⁻¹ a)(l b) = 1 + a b`). Formally, the relation of `X₀` reads
  as the relation for the pair `(scaleHom l ≫ x.hom, scaleHom 1 ≫ X₀.negative)`, and the
  published `relationOver_scaleHom` turns it into the relation for
  `(x.hom, scaleHom l ≫ X₀.negative)`.
- `linked` (definition): the chosen such `X`. `linked_positive` gives `X.positive = x.hom`,
  and `xpPoint_linked` gives `X.xpPoint c = x.rationalPoint c`.
- `oppositeProduct_mul_inv c hq hq₁`: for a unit `c`, let `q` be an opposite factor pair of
  `x(c)` and `q₁` one of `x(1)`. Then
  `(q.1 x(c) q.2) (q₁.1 x(1) q₁.2)⁻¹ = cocharacterPoint p.inclusion (coroot r) c`. By
  uniqueness, both pairs are the explicit pairs of `linked`. Then apply `triple_eq` at `c`
  and at `1`.

## Use

In the `A₂`-orbit case of `Z(k) ⊆ G(k)^+` for quasi-split simply connected groups, the
merged-root coordinate of a rational root-group point determines its opposite-pair product
through `oppositeProduct_mul_inv`. The coroot factors of the rank-one Gauss decompositions
come from `oppositeProduct_mul_mem_range` (module `Rational.PieceCorootFactorization`).

## Provenance

Internal glue between published Library results: linked parametrizations, opposite-pair
existence and uniqueness, and the rescaling lemmas of `LocalWeylNormalizationField`.
Mathematically these are the `SL₂` facts `n(x(c)) = α^∨(c) n(x(1))` and
`n(x(c)) n(x(c')) ∈ α^∨(k^×)`. The module makes no new assertion beyond them.
