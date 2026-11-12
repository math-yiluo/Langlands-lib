# Convergence of the hyperext spectral sequence for bounded objects: proof

Author: Worker 199.

This module proves the published proposition
`Langlands.Cohomology.HyperextConvergence.HyperextConvergenceStatements` of
`Langlands.Cohomology.HyperextConvergence.Statement`:

```
theorem hyperextConvergenceStatements_proof : HyperextConvergenceStatements.{v, u} C
```

Here `C` is any category with the instances of the statement module: preadditive, with a zero
object, a shift by `ℤ` through additive functors, pretriangulated and `IsTriangulated`. The
universes `v` and `u` are independent. Nothing is assumed about `B`. The theorem is the pair
`⟨hyperextPageDegeneration, hyperextStablePage⟩` of the two conjuncts. Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` are used.

## Notation

Fix a t-structure `t` on `C`, objects `K` and `B`, and integers `a`, `b` with `t.IsGE K a` and
`t.IsLE K b`. Write `t'` for `opTStructure t` and `X` for `hyperextSpectralObject t K B`. By
definition, `X.H n = t'.ω₁ ⋙ (preadditiveYoneda.obj B).shift n`. The shifted functor
`(preadditiveYoneda.obj B).shift n` is `preadditiveYoneda.obj (B⟦n⟧)`. So `H^n(i ⟶ j)` is the
group of morphisms from `(τ_{≥ i} τ_{< j} (op K)).unop` to `B⟦n⟧`, where the truncations
`eTruncGE`, `eTruncLT` are those of `t'`. The truncation `eTruncGE ⊥` is the identity functor,
and so is `eTruncLT ⊤`. In particular `H^n(⊥ ⟶ ⊤)` is `K ⟶ B⟦n⟧`. Since `K` lies in degrees
`≥ a` and `≤ b` for `t`, `op K` lies in degrees `≥ -b` and `≤ -a` for `t'`.

## An abstract description of `E` (`eAddEquiv`)

Section `Abstract` treats any spectral object `X` in `AddCommGrpCat` indexed by a category `ι`.
It fixes morphisms `f₁ : i ⟶ j`, `f₂ : j ⟶ k`, `f₃ : k ⟶ l`, `fik` with `f₁ ≫ f₂ = fik`, and
`fil` with `fik ≫ f₃ = fil`. Let `A` and `B` be subgroups of `H^{n₁}(fil)`. Suppose `A` is the
image of `H^{n₁}(fik) ⟶ H^{n₁}(fil)` and `B` is the image of `H^{n₁}(f₁) ⟶ H^{n₁}(fil)`. Both
maps are induced by `twoδ₂Toδ₁`. Then `eAddEquiv` is an additive equivalence

```
E^{n₁}(f₁, f₂, f₃) ≃+ A ⧸ B.addSubgroupOf A.
```

Proof. Mathlib's `cokernelSequenceE` is an exact sequence

```
H^{n₁}(f₁) ⊞ H^{n₀}(f₃) ⟶ H^{n₁}(fik) ⟶ E^{n₁}(f₁, f₂, f₃) ⟶ 0
```

(`cokernelSequenceE_exact`). On the first summand its first map is `H^{n₁}(f₁) ⟶ H^{n₁}(fik)`.
On the second summand it is the connecting map `δ`. Let `ψ` be the composite of
`H^{n₁}(fik) ⟶ A` and the projection `A ⟶ A ⧸ B`. Then `ψ` is surjective because `A` is the
image. The proof shows that the kernel of `ψ` equals the kernel of
`H^{n₁}(fik) ⟶ E^{n₁}(f₁, f₂, f₃)`. By exactness the latter is the image of the first map.

* An element of that image maps to `B`. On the first summand this holds because
  `H^{n₁}(f₁) ⟶ H^{n₁}(fik) ⟶ H^{n₁}(fil)` is the map defining `B`. On the second summand,
  `δ` followed by `H^{n₁}(fik) ⟶ H^{n₁}(fil)` vanishes (`zero₁`).
* Conversely, let `x` map into `B`, say to the image of `y ∈ H^{n₁}(f₁)`. Then `x` minus the
  image of `y` lies in the kernel of `H^{n₁}(fik) ⟶ H^{n₁}(fil)`. By the exact sequence `exact₁`
  of the spectral object, this kernel is the image of `δ`. Hence `x` lies in the image of the
  first map.

Both groups are then quotients of `H^{n₁}(fik)` by the same subgroup. The equivalence composes
`quotientKerEquivOfSurjective` (twice) with `quotientAddEquivOfEq`.

## Vanishing outside the rows `-b ≤ q ≤ -a`

`isZero_H_of_isZero` shows that `H^n(D)` vanishes when `(t'.ω₁.obj D).obj (op K)` is zero. It
applies `Functor.map_isZero` to the shifted Yoneda functor.

* `isZero_H_bot`: for `c ≤ -b`, `H^n(⊥ ⟶ c)` vanishes, because `τ_{< c} (op K)` is zero
  (`isZero_eTruncLT_obj_obj`).
* `isZero_H_top`: for `-a < c`, `H^n(c ⟶ ⊤)` vanishes, because `τ_{≥ c} (op K)` is zero
  (`isZero_eTruncGE_obj_obj`).
* `isZero_page_X_of_lt`, `isZero_page_X_of_gt`: if `q < -b` or `-a < q`, the object in position
  `(p, q)` of every page `r ≥ 2` is zero. Mathlib's `isZero_spectralSequence_page_X_of_isZero_H'`
  for `coreE₂Cohomological` reduces this to the vanishing of `H^{p+q}(q ⟶ q + 1)`. This group
  is `Hom` out of `τ_{≥ q} τ_{< q + 1} (op K)`. For `q < -b` the inner truncation `τ_{< q + 1}`
  is zero, because `q + 1 ≤ -b`. For `-a < q` the outer truncation `τ_{≥ q}` is zero, because
  `τ_{< q + 1} (op K)` still lies in degrees `≤ -a` for `t'`.

## Page degeneration (`hyperextPageDegeneration`)

Let `r ≥ 2` and `b - a + 2 ≤ r`. Consider the differential from `(p, q)` to `pq'`. If the two
positions are not related by the shape `ComplexShape.up' (r, 1 - r)`, the differential is zero
(`HomologicalComplex.shape`). Otherwise `pq' = (p + r, q + 1 - r)`. If `q < -b` or `-a < q`, the
source is zero. If `-b ≤ q ≤ -a`, the target row satisfies `q + 1 - r ≤ -a + 1 - (b - a + 2) < -b`.
So the target is zero.

## Membership in the filtration (`mem_filtration_iff_exists`)

Let `m` be an integer with `p - n = 1 - m`. Then `f : K ⟶ B⟦n⟧` lies in `F^p` exactly when
`f = ι_m ≫ x` for some `x : (τ_{< m} (op K)).unop ⟶ B⟦n⟧`. Here `ι_m` is
`((t'.truncLTι m).app (op K)).unop : K ⟶ (τ_{< m} (op K)).unop`. In `C` the target of `ι_m` is
the truncation `τ_{≥ 1 - m} K`, but the proof does not use this identification.

Proof. By `mem_filtration_iff_truncLTι_comp_eq_zero`, `f ∈ F^p` means that
`(t.truncLTι (p - n)).app K ≫ f = 0`. Let `T` be the distinguished triangle of `C` obtained by
applying `triangleOpEquivalence` to the truncation triangle `triangleLTGE m` of `op K` for `t'`.
Its second morphism is `ι_m`. Its first object `(τ_{≥ m} (op K)).unop` lies in degrees `≤ -m`
for `t`.

* If `f ∈ F^p`, the first morphism of `T` factors through `t.truncLTι (1 - m)`
  (`liftTruncLT`, as `-m + 1 = p - n`). Hence it is killed by `f`, and `Triangle.yoneda_exact₂`
  factors `f` through `ι_m`.
* If `f = ι_m ≫ x`, then `(t.truncLTι (p - n)).app K ≫ ι_m` goes from an object in degrees
  `≤ p - n - 1 = -m` to `(τ_{< m} (op K)).unop`. That object lies in degrees `≥ 1 - m` for `t`
  (`opTStructure_isLE_iff`). So this composite is zero (`TStructure.zero`).

`H_map_twoδ₂Toδ₁_apply` records that the map `H^n(⊥ ⟶ m) ⟶ H^n(⊥ ⟶ ⊤)` of `X` (along
`twoδ₂Toδ₁`) sends `x` to `ι_m ≫ x`. The proof unfolds the definitions by `change` and uses
`Category.id_comp`.

## The stable pages in the rows `-b ≤ q ≤ -a` (`stablePageIsoOfMem`)

Let `r ≥ 2`, `b - a + 2 ≤ r`, and `-b ≤ q ≤ -a`. Put `n = p + q`. The isomorphism is a
composite of four isomorphisms.

1. `spectralSequencePageXIso` for `coreE₂Cohomological` identifies the object in position
   `(p, q)` of page `r` with `E^n(q - r + 2 ⟶ q ⟶ q + 1 ⟶ q + r - 1)`.
2. Since `q - r + 2 ≤ -b`, the group `H^{n+1}(⊥ ⟶ q - r + 2)` vanishes (`isZero_H_bot`).
   Mathlib's `isoMapFourδ₁Toδ₀'` (inverted) then replaces the first index by `⊥`. This gives
   `E^n(⊥ ⟶ q ⟶ q + 1 ⟶ q + r - 1)`.
3. Since `-a < q + r - 1`, the group `H^{n-1}(q + r - 1 ⟶ ⊤)` vanishes (`isZero_H_top`).
   Mathlib's `isoMapFourδ₄Toδ₃'` then replaces the last index by `⊤`. This gives
   `E^n(⊥ ⟶ q ⟶ q + 1 ⟶ ⊤)`.
4. `eAddEquiv` with `i = ⊥`, `j = q`, `k = q + 1`, `l = ⊤` gives the final isomorphism, through
   `AddEquiv.toAddCommGrpIso`. The subgroups are `A = F^p` and `B = F^{p+1}` of
   `H^n(⊥ ⟶ ⊤) = Hom(K, B⟦n⟧)`. The image hypotheses come from `mem_filtration_iff_exists`
   with `m = q + 1` for `F^p` (`p - n = -q`) and `m = q` for `F^{p+1}` (`p + 1 - n = 1 - q`),
   together with `H_map_twoδ₂Toδ₁_apply`. The resulting quotient is
   `HyperextAbutment.graded t K B (p + q) p`.

## Stable pages (`hyperextStablePage`)

If `-b ≤ q ≤ -a`, the isomorphism is `stablePageIsoOfMem`. Otherwise both sides are zero, and
`IsZero.iso` gives the isomorphism.

* The page object is zero by `isZero_page_X_of_lt` or `isZero_page_X_of_gt`.
* `gr^p` is trivial, and `AddCommGrpCat.isZero_of_subsingleton` shows it is a zero object. For
  `q < -b`, triviality is the published `subsingleton_graded_of_isLE`, since `b < p - (p + q)`
  (`subsingleton_graded_of_lt`). For `-a < q`, `F^p ≤ F^{p+1}`
  (`subsingleton_graded_of_gt`). Membership in `F^{p+1}` asks a morphism to vanish on
  `τ_{< 1 - q} K`. That truncation is zero because `K` lies in degrees `≥ a ≥ 1 - q`
  (`isZero_truncLT_obj_of_isGE`).

## Relation to the route in the statement Markdown

The proof follows the five steps of the statement Markdown. Steps 3 and 4 there describe the
stable term as the image of `Hom(τ_{≥ -q} K, B⟦n⟧) → Hom(τ_{≤ -q} K, B⟦n⟧)`. Instead, the Lean
proof goes through the abstract quotient description `eAddEquiv` of
`E^n(⊥ ⟶ q ⟶ q + 1 ⟶ ⊤)` inside `Hom(K, B⟦n⟧)`. It then identifies the two subgroups with
`F^p` and `F^{p+1}` directly.
