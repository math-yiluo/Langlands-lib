# Fixed rational points of a matrix-equivariant closed subscheme of projective space

This is a helper module for the proof of
`Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement`, which is Milne's
*Algebraic Groups* (2017), Proposition 20.11, printed pp. 410–411 (PDF pp. 426–427). It
transfers the coordinate result `ProjectiveSpace.exists_weightBlock_points` (module
`Langlands.AlgebraicGeometry.ProjectiveSpace.WeightBlockPoints`) to a scheme `X` with a group
action and an equivariant closed immersion into projective space. It does not assume that the
acting group is a torus. Instead it takes as hypotheses a change of basis `P` and integral
weights `m`, with the two properties that the module
`Langlands.GroupScheme.SplitTorusGenericWeights` proves for split tori.

Notation. `k` is a field and `pt` is the base test `Over.mk (𝟙 (Spec k))`. A morphism
`pt ⟶ X` is a rational point of `X`, and `cp` is the closed point of `Spec k`. The ambient
scheme `ProjectiveOrbit.ambient n (CommRingCat.of k)` is relative projective `n`-space over
`Spec k`. `ProjectiveSpace k n = Proj k[X_0, …, X_n]` is polynomial projective space. A point
`y` of it has homogeneous coordinates `c` when `HasCoordinates y c` holds (module
`Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointZeros`).
`ProjectiveSpace.linearAction k n e` is the automorphism of `ProjectiveSpace k n` induced by
a linear equivalence `e`. `ProjectiveOrbit.coordinateEquiv n M` is the linear equivalence
`v ↦ M *ᵥ v` of an invertible matrix `M`. `ρ.rationalMatrix` is the homomorphism from rational
points of the group to `GL (Fin (n + 1)) k` defined by a matrix representation `ρ`.

## Main result

`ProjectiveTorusFixedPoint.exists_fixed_points_of_frame`. Assume the following:

- `k` is algebraically closed;
- `H` is a group scheme over `Spec k` with `H.X.hom` smooth;
- `X` is an object over `Spec k` with `X.hom` locally of finite type;
- `a : SchemeAction H X` and `ρ : MatrixRepresentation H (Fin (n + 1))`;
- `φ : X ⟶ ambient n k` has `φ.left` a closed immersion, and
  `IsMatrixEquivariant a ρ φ` holds;
- `P : GL (Fin (n + 1)) k` and `m : Fin (n + 1) → ℤ` satisfy:
  - (`hμ`) for every `z : kˣ` there is a rational point `t` of `H` with
    `ρ.rationalMatrix t = P · diagonal (z ^ m i)_i · P⁻¹`;
  - (`hblock`) for every rational point `t` of `H` there is `χ : Fin (n + 1) → kˣ` with
    `χ i = χ l` whenever `m i = m l`, and `ρ.rationalMatrix t = P · diagonal χ · P⁻¹`;
- `d : ℕ` satisfies `d ≤ topologicalKrullDim X.left`.

Then there is an injective family `x : Fin (d + 1) → (pt ⟶ X)` with `a.IsFixed (x j)` for
every `j`. Here `a.IsFixed` is fixedness on all test schemes, not only on rational points.

## Proof as implemented

Write `ι := embedding φ : X.left ⟶ ProjectiveSpace k n` (defined below), and let `e` be the
linear equivalence `v ↦ P *ᵥ v`.

1. *Separatedness.* `X.hom = φ.left ≫ (ambient n k).hom` (`Over.w φ`). The Library instance
   `ambient_isSeparated` and the closed immersion `φ.left` make `X.hom` separated.
2. *The closed set.* Let `Z` be the range of `ι ≫ (linearActionIso k n e).inv`. This is the
   image of `X` in the coordinates given by the columns of `P`. The composite is a closed
   immersion, so `Z` is closed. Its corestriction `X.left → Z` is inducing
   (`Topology.IsInducing.codRestrict`), so `topologicalKrullDim X.left ≤ topologicalKrullDim Z`
   (`Topology.IsInducing.topologicalKrullDim_le`). Hence `d ≤ topologicalKrullDim Z`.
3. *Lifting.* A point `y` of `Z` with coordinates `c` gives the point `linearAction e y` of the
   range of `ι`, with coordinates `P *ᵥ c` (`HasCoordinates.linearAction`). By
   `exists_rationalPoint`, there is a rational point `x` of `X` such that `ι (x cp)` has
   coordinates `P *ᵥ c`.
4. *Stability.* Let `y ∈ Z` have coordinates `c`, and let `z : kˣ`. Lift `y` to `x` as in
   step 3. Take `t` from `hμ z`. By `act_embedding_apply`, `ι ((a.act t x) cp)` is
   `linearAction (ρ.rationalMatrix t)` applied to `ι (x cp)`. So it has coordinates
   `P D P⁻¹ (P *ᵥ c) = P *ᵥ (z ^ m i * c i)_i` (`conj_diagonal_mulVec`). Any point `y'` with
   coordinates `(z ^ m i * c i)_i` has `linearAction e y'` with the same coordinates.
   Then `HasCoordinates.eq` gives `linearAction e y' = ι ((a.act t x) cp)`, so `y' ∈ Z`. This
   is the stability hypothesis of `exists_weightBlock_points`.
5. *Points.* `exists_weightBlock_points Z` gives `d + 1` pairwise non-proportional nonzero
   vectors `c j`. Each is supported on one level set of `m`, and every point with coordinates
   `c j` lies in `Z`. Step 3 (with `exists_hasCoordinates`) gives rational points `x j` such
   that `ι (x j cp)` has coordinates `P *ᵥ c j`.
6. *Injectivity.* If `x j = x j'`, then one point has coordinates `P *ᵥ c j` and `P *ᵥ c j'`.
   So `P *ᵥ c j' = b • P *ᵥ c j` for some `b` (`HasCoordinates.exists_eq_smul`), and hence
   `c j' = b • c j` because `e` is injective. This is impossible for `j ≠ j'`.
7. *Fixedness.* `X.hom` is separated and `H` is smooth, so by the Library theorem
   `SchemeAction.isFixed_iff_rationalPoints` it suffices to show `a.act t (x j) = x j` for
   every rational point `t` of `H`. Take `χ` from `hblock t`, and pick `i0` with
   `c j i0 ≠ 0`. Every `i` with `c j i ≠ 0` has `m i = m i0`, so `χ i = χ i0`. Hence
   `(χ i * c j i)_i = χ i0 • c j`. As in step 4, `ι ((a.act t (x j)) cp)` has coordinates
   `P *ᵥ (χ i * c j i)_i = χ i0 • (P *ᵥ c j)`. These are also coordinates of `ι (x j cp)`
   (`HasCoordinates.smul`, since `χ i0` is a unit). So the two points of projective space are
   equal. A closed immersion is injective, so `(a.act t (x j)) cp = x j cp`. Two `k`-points of
   a scheme locally of finite type over algebraically closed `k` that agree at the closed point
   are equal (Mathlib's `AlgebraicGeometry.ext_of_apply_closedPoint_eq`).

## Helper declarations

In the namespace `Langlands.AlgebraicGeometry.ProjectiveSpace`:

- `HasCoordinates.eq`: two points of `ProjectiveSpace K n` with the same homogeneous
  coordinates are equal. The homogeneous primes of both points have the same homogeneous
  elements, namely those vanishing at the coordinates.
- `linearActionIso_inv_apply_linearAction`, `linearAction_linearActionIso_inv_apply`: on points,
  `linearAction K n e` and `(linearActionIso K n e).inv` are mutually inverse.

In the namespace `Langlands.GroupScheme.ProjectiveTorusFixedPoint`:

- `embedding φ := φ.left ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec k))`. This is the
  morphism to polynomial projective space underlying `φ`.
  - `embedding_toSpec`: `embedding φ` lies over `Spec k`.
  - `isClosedImmersion_embedding`: it is a closed immersion when `φ.left` is, because
    `toPolynomial` along the identity is an isomorphism (`RelativeProjectiveSpace.map_id`).
- `pointSection_eq`: for a rational point `y` of the ambient space,
  `ProjectiveOrbit.pointSection y = y.left`.
- `act_embedding` and `act_embedding_apply`: equivariance on rational points.
  `(a.act h x).left ≫ embedding φ` equals
  `x.left ≫ embedding φ ≫ linearAction (coordinateEquiv n (ρ.rationalMatrix h))`. The proof
  specializes `IsMatrixEquivariant` to the base test and uses the Library theorems
  `RelativeProjectiveSpace.map_toPolynomial` and `ProjectiveOrbit.matrixAction_toPolynomial`.
  The `_apply` version is the same identity evaluated at the closed point.
- `exists_rationalPoint`: let `k` be algebraically closed and `embedding φ` locally of finite
  type. A point of the range of `embedding φ` with coordinates `c` is the image of a rational
  point of `X`. The rational point of projective space with coordinates `c`
  (`Proj.fromOfGlobalSections` at evaluation in `c`) is lifted along `embedding φ` by the
  Library theorem `exists_rationalPoint_lift_of_mem_range`.
- `conj_diagonal_mulVec`: `(P · diagonal D · P⁻¹) *ᵥ (P *ᵥ v) = P *ᵥ (D i * v i)_i`.

## Relation to the source

Milne's proof of Proposition 20.11 uses his Lemma 13.51 to replace `T` by `G_m`, acting
through a cocharacter `μ`. It then works in a basis `e_0, …, e_n` of eigenvectors with
`μ(t) e_i = t ^ m_i e_i`. The hypotheses `hμ` and `hblock` record these choices on rational
points. `hμ` says that the rational points `μ(z)` act diagonally with weights `m` in the basis
given by the columns of `P`. `hblock` says that every rational point of the torus acts by a
scalar on each weight space of `μ`, so that a point fixed by `μ` in this sense is fixed by the
whole torus. Step 7 is the argument that a point whose coordinates lie in one weight space of
`μ` is fixed by the torus. The passage from fixedness on rational points to fixedness
on all tests uses the smoothness of the acting group, through the Library theorem
`isFixed_iff_rationalPoints`. Milne works with varieties and does not need this step.
