# Solvability of the closure of a group of rational points

Module `Langlands.GroupScheme.Absolute.RationalPointClosureSolvable` is helper
infrastructure for the proof of `NormalUnipotentBorelContainmentStatement`. It has two
parts:

- the `k`-points located in the Zariski closure of a group `Γ` of `k`-points form a
  group, which is solvable when `Γ` is solvable (section `Closure`);
- over an algebraically closed field, the Library's `IsSolvableGroupScheme` is solvability
  of the group of `k`-points (section `AlgClosed`).

Throughout, `k` is a field, `H` a group scheme over `Spec k`, and "point" means a
`k`-point `Over.mk (𝟙 (Spec k)) ⟶ H.X`. Its location is the image of the closed point of
`Spec k`, as in `rationalPointImage` (`Absolute.RationalPointClosureStatement`).

## Closure of a set of points

- `rationalPointClosure H S` is the set of points whose location lies in the closure of
  `rationalPointImage H S`. `subset_rationalPointClosure` and `rationalPointClosure_mono`
  are immediate.
- `comp_mem_rationalPointClosure`: let `φ : H.X ⟶ H.X` be a morphism over `Spec k` such
  that `s ≫ φ` lies in the closure of `S'` for all `s ∈ S`. Then `x ≫ φ` lies in the
  closure of `S'` for every `x` in the closure of `S`. The location of `x ≫ φ` is the
  image of the location of `x` under the continuous map `φ.left`.
- `mem_rationalPointClosure_of_binary`: let `w` be a binary operation on points such that
  `y ↦ w a y` and `x ↦ w x b` are each given by composition with a morphism
  `H.X ⟶ H.X`. If `w` sends `A × B` into the closure of `C`, it sends (closure of `A`) ×
  (closure of `B`) there too. The proof applies the previous lemma twice, once in each
  variable. It does not use any topology on a product.
- Left and right translation by a point `a`, and the commutator maps `y ↦ ⁅a, y⁆` and
  `x ↦ ⁅x, b⁆`, are composition with morphisms `H.X ⟶ H.X`. These morphisms are built from
  the constant point `H.constantPoint a H.X` and `𝟙 H.X` with the group operations on
  `H.X ⟶ H.X` (`exists_comp_eq_mul_left`, `exists_comp_eq_mul_right`,
  `exists_comp_eq_commutator_left`, `exists_comp_eq_commutator_right`). The helper lemmas
  `comp_constantPoint` and `comp_commutatorElement` compute the compositions.

## The closure subgroup

- `pointClosureSubgroup H Γ`, for a subgroup `Γ` of the points, has carrier
  `rationalPointClosure H Γ`. Closure under products uses the binary lemma with
  multiplication. Closure under inverses uses `comp_mem_rationalPointClosure` with the
  inverse morphism `(𝟙 H.X)⁻¹`. This is Milne, *Algebraic Groups* (2017), Lemma 1.40
  (printed p. 18, zero-based PDF page 33), proved through translation morphisms rather
  than neighbourhoods. `mem_pointClosureSubgroup`, `le_pointClosureSubgroup` and
  `pointClosureSubgroup_mono` record its basic properties.
- `commutator_pointClosureSubgroup_le`: `⁅cl A, cl B⁆ ≤ cl ⁅A, B⁆`. It applies the binary
  lemma to the commutator operation.
- Now let `k` be algebraically closed and `H.X` locally of finite type over `Spec k`.
  Mathlib's `pointEquivClosedPoint` shows that the location of a point is a closed point
  (`isClosed_singleton_rationalPoint`). Mathlib's `ext_of_apply_closedPoint_eq` shows that
  a point is determined by its location (`rationalPoint_ext`). Hence
  `pointClosureSubgroup_bot`: the closure of the trivial subgroup is trivial.
- `map_derivedSeries_pointClosureSubgroup_le`: by induction on `n`, the `n`-th derived
  subgroup of `cl Γ`, viewed in the ambient group of points, lies in the closure of the
  `n`-th derived subgroup of `Γ`. The successor step is `commutator_pointClosureSubgroup_le`.
- `isSolvable_pointClosureSubgroup`: under the same hypotheses on `k` and `H`, if `Γ` is
  solvable then so is `cl Γ`. If the `n`-th derived subgroup of `Γ` is trivial, the
  previous two items show that the `n`-th derived subgroup of `cl Γ` is trivial.

## Solvability over an algebraically closed field

The Library's `IsSolvableGroupScheme G` (`Absolute.Borel`) asks that the group of
`k̄`-points of the base change of `G` to `k̄ = AlgebraicClosure k` be solvable.

- `isIso_toAlgebraicClosure`: if `k` is algebraically closed, `algebraMap k k̄` is
  bijective (`IsAlgClosed.algebraMap_bijective_of_isIntegral`). So the morphism
  `toAlgebraicClosure k : Spec k̄ ⟶ Spec k` is an isomorphism.
- `algebraicClosurePointIso`: the corresponding isomorphism of objects over `Spec k`,
  between `Spec k̄` (via `toAlgebraicClosure k`) and the identity of `Spec k`.
- `pointsMulEquivOfIso`: in a cartesian monoidal category, an isomorphism `T ≅ T'` induces
  a group isomorphism `(T' ⟶ G) ≃* (T ⟶ G)` for a group object `G`.
- `isSolvableGroupScheme_iff_isSolvable_points`: over an algebraically closed `k`,
  `IsSolvableGroupScheme G` holds exactly when the group of `k`-points of `G` is solvable.
  The Library's `baseChangePointsEquiv` identifies the `k̄`-points of the base change with
  the points of `G` on `Spec k̄`. The previous item identifies these with the `k`-points.
  Solvability passes along the resulting group isomorphism in both directions.

## Provenance

Only `pointClosureSubgroup` has a literature counterpart, Milne's Lemma 1.40. The
remaining declarations are internal proof infrastructure: the standard argument that
commutators of closures lie in the closure of commutators, and a comparison of the
Library's definition of solvability with solvability of `k`-points.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
