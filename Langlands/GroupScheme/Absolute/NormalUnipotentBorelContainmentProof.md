# Proof: normal unipotent subgroups lie in every Borel subgroup

Module `Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof` proves

```lean
theorem Langlands.GroupScheme.normalUnipotentBorelContainment :
    NormalUnipotentBorelContainmentStatement.{u}
```

Let `k` be an algebraically closed field and `H` a smooth, affine, connected group scheme over
`Spec k`. Let `i : U ⟶ H` be a closed subgroup with `U` smooth, connected and unipotent, whose
range is normal in `H` on every test scheme. The theorem shows that the range of `i` lies in the
range of every Borel subgroup `c : C ⟶ H`, on every test scheme.

The theorem is `normalUnipotentBorelContainment_of_rationalPointClosure` applied to
`rationalPointClosureSubgroup : RationalPointClosureSubgroupStatement.{u}`
(`Absolute.RationalPointClosureProof`).

## Route

Milne, *Algebraic Groups* (2017), Remark 17.31 (printed p. 361) derives the containment from the
conjugacy of Borel subgroups. The Lean proof does not use conjugacy. It uses the classical
argument with maximality of `c`. The Zariski closure of `U(k)·C(k)` is a smooth connected solvable
closed subgroup containing `C`, so it equals `C`, and `U(k) ⊆ C(k)`. All groups below are groups
of `k`-points `Over.mk (𝟙 (Spec k)) ⟶ X`, and the closure of a group `Γ` of `k`-points is
`pointClosureSubgroup H Γ` (`Absolute.RationalPointClosureSolvable`).

## Auxiliary lemmas

- `isSolvable_sup_of_normal`: in any group, if `N` is normal and `N`, `K` are solvable, then
  `N ⊔ K` is solvable. The composite `N ⊔ K → G ⧸ N` has kernel inside `N`, so
  `Group.isSolvable_of_ker_le_range` applies. Its range is the image of `K`, which is solvable as
  a surjective image of `K`.
- `range_left_subset_closure`: let `X` be locally of finite type over `Spec k` and
  `f : X ⟶ H.X` a morphism that sends every `k`-point of `X` into a set `S`. Then the
  set-theoretic image of `f` lies in the closure of `rationalPointImage H S`. `X` is a Jacobson
  space (`LocallyOfFiniteType.jacobsonSpace`), so its closed points are dense
  (`closure_closedPoints`). Each closed point is the location of a `k`-point
  (`pointOfClosedPoint`). Continuity of `f` finishes the proof.
- `mem_range_of_location_mem`: let `ζ : Z ⟶ H` be a closed subgroup, with `Z` and `H` locally
  of finite type. A `k`-point `x` of `H` whose location lies in the image of `ζ` is in the range
  of `ζ`. Its location is a closed point (`isClosed_singleton_rationalPoint`). Its preimage
  under the injective map `ζ` is a closed singleton `{z}`. The point `z` gives a `k`-point `y`
  of `Z`. The points `y ≫ ζ` and `x` have the same location, so they are equal
  (`rationalPoint_ext`).

## Main argument (`normalUnipotentBorelContainment_of_rationalPointClosure`)

Assume `RationalPointClosureSubgroupStatement.{u}` and fix the data above.

1. Instances. `U` and `C` are smooth and connected (the second from `IsBorelSubgroup`), and
   `U` is affine over `Spec k` (`IsClosedSubgroup.isAffineHom`). Smoothness over a field gives
   reducedness of `U` and `C`
   (`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`).
2. Let `N` and `K` be the `k`-points of the ranges of `i` and `c`, subgroups of `H(k)`.
   - `N` is normal by the normality premise.
   - `N` is solvable: `U(k)` is solvable by Kolchin's theorem for points
     (`isSolvable_points_of_isUnipotent`, `Absolute.UnipotentPointsSolvable`), and `N` is its
     image.
   - `K` is solvable: `C(k)` is solvable by `isSolvableGroupScheme_iff_isSolvable_points`, and
     `K` is its image.

   Hence `Γ := N ⊔ K` is solvable (`isSolvable_sup_of_normal`).
3. The assumed statement, applied to `H` and `Γ`, gives a smooth group scheme `Z` and a closed
   subgroup `ζ : Z ⟶ H` whose image is the closure of `rationalPointImage H Γ`. So:
   - every point of `pointClosureSubgroup H Γ` lies in the range of `ζ`
     (`mem_range_of_location_mem`);
   - for every `k`-point `y` of `Z`, `y ≫ ζ` lies in `pointClosureSubgroup H Γ`.
4. `Z` is solvable. `ζ` is a monomorphism, so `y ↦ y ≫ ζ` embeds `Z(k)` into
   `pointClosureSubgroup H Γ`. That group is solvable by `isSolvable_pointClosureSubgroup`.
   Then `Group.isSolvable_of_isSolvable_injective` and
   `isSolvableGroupScheme_iff_isSolvable_points` apply.
5. `Z` is connected. For `a ∈ N`, let `φ a : H.X ⟶ H.X` be left translation by `a`
   (`exists_comp_eq_mul_left`). Let `A` be the image of `i` and `B a` the image of `c ≫ φ a`.
   - `A` and `B a` are preconnected as continuous images of connected spaces.
   - The location of `a` lies in `A ∩ B a`: `a = y ≫ i` for some `y`, and `a = 1 ≫ c ≫ φ a`.
   - Every `A ∪ B a` contains the image of a fixed point of the nonempty space `U`. So
     `Y := ⋃ₐ (B a ∪ A)` is preconnected (`isPreconnected_iUnion`).
   - `Y` lies in the closure of `rationalPointImage H Γ` by `range_left_subset_closure`: the
     `k`-points of `C` go to `a · K ⊆ Γ` and those of `U` go to `N ⊆ Γ`.
   - Conversely `rationalPointImage H Γ ⊆ Y`. By normality every element of `Γ` is `n * z`
     with `n ∈ N` and `z = y ≫ c ∈ K` (`Subgroup.mem_sup_of_normal_left`). Then
     `n * z = y ≫ c ≫ φ n`, located in `B n`.

   Hence the closure of `rationalPointImage H Γ` is preconnected
   (`IsPreconnected.subset_closure`). It is the image of `ζ`, a closed embedding, so `Z.X.left`
   is preconnected. It is nonempty because it contains the identity point.
6. Factorization and maximality. The `k`-points of the range of `c` lie in
   `K ≤ Γ ≤ pointClosureSubgroup H Γ`, hence in the range of `ζ`. Since `C` is reduced,
   `SubgroupFunctor.exists_factor_of_algClosed_points` gives `f : C ⟶ Z` with `f ≫ ζ = c`.
   The maximality field of `IsBorelSubgroup c` applies to the smooth, connected, solvable closed
   subgroup `ζ`, so `f` is an isomorphism and `ζ = inv f ≫ c`.
7. Containment. `U` is reduced, so by `SubgroupFunctor.range_le_of_algClosed_points` it
   suffices to compare `k`-points. Every `x ∈ N` lies in `Γ`, hence in the range of `ζ`. So
   `x = y ≫ ζ = (y ≫ inv f) ≫ c`, which is in the range of `c`.

## Provenance

The statement `NormalUnipotentBorelContainmentStatement` is sourced in its own Markdown
(Milne 2017, Remark 17.31). This proof and its helper lemmas are internal. The inputs from other
modules are Kolchin's theorem for points (`Absolute.UnipotentPointsSolvable`), the closure
subgroup and its solvability (`Absolute.RationalPointClosureSolvable`), the smooth closed subgroup
on the closure (`Absolute.RationalPointClosureProof`), and the published Library lemmas named
above.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
