# Products of additive embeddings with independent torus weights: proof

This module proves the proposition
`Langlands.GroupScheme.IndependentWeightProductImmersionStatement.{u}` from the
module `Langlands.GroupScheme.Rational.IndependentWeightProductStatement`. The
statement pair is unchanged.

## Main theorem

`Langlands.GroupScheme.independentWeightProductImmersion :
IndependentWeightProductImmersionStatement.{u}`.

Fix a field `k`, an affine group scheme `G` over `Spec k`, a split torus `S`, an
automorphic action `b` of `S` on `G`, factors `y i : Ga ⟶ G` for `i : Fin r`
that are closed subgroups, and `ℤ`-linearly independent weights `w i`. Each
factor must satisfy the scaling hypothesis `hy`: on every scheme test, `b.act s`
sends the image of the scalar point `c` under `y i` to the image of
`charValue (w i) s * c`. Write `φ = IndependentWeightProduct.morphism y` from
standard affine space `V = VectorGroup.groupScheme k r` to `G`. The proof shows
that the coordinate pullback `pullback φ : Coord G →ₐ[k] Coord V` of the
Library's `PointedCoordinateWeights` framework is surjective, and then
concludes with the closed-immersion criterion of the section *Surjective
coordinate pullback* below.

1. By `exists_lift`, for each `j` there is `g j` in the weight space of
   `PointedAction.ofGroup b` for `w j` whose pullback along `y j` is the linear
   coordinate `coordinateFunctions k 1 0` of `Ga`.
2. By `pullback_lift_eq`, `pullback φ (g j) = coordinateFunctions k r j`.
3. So `pullback φ` composed with `MvPolynomial.aeval g` equals
   `MvPolynomial.aeval (coordinateFunctions k r)`, by `MvPolynomial.algHom_ext`.
   That map is surjective (`aeval_coordinateFunctions_surjective`), so
   `pullback φ` is surjective.
4. `isClosedImmersion_of_pullback_surjective` gives
   `IsClosedImmersion φ.left`.

The case `r = 0` needs no separate treatment. The field may be arbitrary; no
smoothness or connectedness of `G` is used.

All auxiliary declarations are in the namespace
`Langlands.GroupScheme.IndependentWeightProduct`. A local instance records that
`VectorGroup.groupScheme k n` is affine over `Spec k`
(`VectorGroup.isAffineHom_groupScheme`). The file sets
`backward.isDefEq.respectTransparency false`, as other Library files in this
directory do.

## A diagonal torus action on standard affine space

For characters `u : Fin n → characterLattice S`, `diagonalPointAction u T s v`
scales the `i`-th coordinate of a scheme-valued point `v` by
`VectorGroup.charValue (u i) T s`. The lemmas `diagonalPointAction_comp`,
`_one`, `_mul` and `_mul_right` are naturality in the test, the unit and
multiplication laws in `s`, and additivity in `v`. They are checked
coordinatewise with `VectorGroup.points_ext`. They feed the Library's
`AutomorphicAction.ofPoints`, which yields `diagonalAction u :
AutomorphicAction S.toGrp (VectorGroup.groupScheme R n)`. `diagonalAction_act`
evaluates it on points.

- `vectorCoordinates_affinePoint` computes the coordinates of
  `VectorGroup.affinePoint A t` on the affine test `Spec A`: they are the
  images of the parameters `t j` under `(Scheme.ΓSpecIso A).inv`. The proof uses
  `Corepresented.pointsEquiv_eq_affinePointsEquiv` and
  `VectorGroup.affinePointsEquiv_affinePoint`.
- `affinePoint_injective`: `VectorGroup.affinePoint A` is injective.
- `diagonalAction_affinePoint`: on an affine test, the diagonal action of `s`
  sends `affinePoint A t` to `affinePoint A (fun i => characterValue (u i) s * t i)`.
  It identifies `charValue` on `Spec A` with `Lie.characterValue` transported
  by `ΓSpecIso`.

## Actual coordinates of standard affine space

`coordinateFunctions k n : Fin n → Coord V` is the parameter vector of the
universal point `universalPoint V` under `Corepresented.affinePointsEquiv`.
Here `Coord V` is the Library's actual coordinate algebra of `V`.

- `pointsMap_affinePoint` and `pointsMap_universalPoint` show how affine points
  and the universal point behave under change of test algebra.
- `affinePoint_coordinateFunctions`: `affinePoint (coordinateFunctions k n)`
  is the universal point.
- `pointCoordinates_affinePoint_coordinateFunctions`: evaluating the function
  `coordinateFunctions k n j` at `affinePoint A t` gives `t j`.
  `pointCoordinates_affinePoint_aeval` extends this to
  `aeval (coordinateFunctions k n) P ↦ aeval t P` for polynomials `P`.
- `aeval_coordinateFunctions_surjective`: every `z : Coord V` is
  `aeval (coordinateFunctions k n) P` for
  `P = pointCoordinates (affinePoint (MvPolynomial (Fin n) k) X) z`. This uses
  naturality of `pointCoordinates` and the universal-point identity.

## Eigenfunctions of the diagonal action

These results concern the Library's `PointedCoordinateWeights.weightSpace`,
whose elements are the eigenfunctions tested on all affine points.

- `characterValue_add` and `characterValue_zero` show that
  `Lie.characterValue` is additive and sends `0` to `1`. They use
  `comp_groupHom_add` and `comp_groupHom_zero`.
- `one_mem_weightSpace`, `mul_mem_weightSpace` and `pow_mem_weightSpace`:
  `1` has weight `0`, weights add under products, and `z ^ e` has weight
  `e • χ` when `z` has weight `χ`. This holds for any pointed action `a` on an
  affine `V`.
- `coordinateFunctions_mem_weightSpace`: the coordinate `coordinateFunctions k n i`
  has weight `u i` for `PointedAction.ofGroup (diagonalAction u)`. Every affine
  point is an `affinePoint` (`VectorGroup.affinePoint_surjective`), so this
  follows from `diagonalAction_affinePoint` and the evaluation formula.
- `aeval_monomial_mem_weightSpace`: the monomial with exponent `m` and
  coefficient `1` has weight `Finsupp.linearCombination ℕ u m`. The proof is by
  `Finsupp.induction_linear`.

## Independent weights of linear coordinates

`eq_smul_coordinateFunctions` assumes `S` is a split torus, `w` is
`ℤ`-linearly independent, and `F : Coord V` has weight `w j` for the diagonal
action with weights `w`. It concludes that `F = c • coordinateFunctions k r j`
for some `c : k`.

- The weight spaces are independent (`iSupIndep`). This comes from
  `DirectSum.IsInternal.submodule_iSupIndep` applied to the first conjunct of
  the published `pointedCoordinateDecomposition`.
- `ℤ`-independence restricts to `ℕ`-independence
  (`LinearIndependent.restrict_scalars`, using injectivity of `ℕ → ℤ`).
- Write `F = aeval (coordinateFunctions k r) P`. Let `c` be the coefficient of
  `P` at the exponent `single j 1`, and let `Q` be `P` minus that monomial.
- The image of `Q` has weight `w j`, as a difference of two elements of that
  weight space.
- Every monomial `m` in the support of `Q` differs from `single j 1`. Its weight
  `linearCombination ℕ w m` therefore differs from
  `w j = linearCombination ℕ w (single j 1)`, by `ℕ`-independence. So the image
  of `Q` also lies in the supremum of the other weight spaces.
- Independence makes the image of `Q` zero, so `F = c • coordinateFunctions k r j`.

## Surjective coordinate pullback

`isClosedImmersion_of_pullback_surjective` assumes `V` and `W` are affine over
`Spec k` and `f : V ⟶ W` has surjective `pullback f`. It concludes
`IsClosedImmersion f.left`. This is the converse of the published
`pullback_surjective_of_isClosedImmersion`. Take left components of the
published `algSpec_map_pullback`. They identify
`(coordinateIso V).hom.left ≫ f.left` with `Spec.map ψ` followed by an
isomorphism, where `ψ` is the underlying ring map of `pullback f`. Mathlib's
`IsClosedImmersion.spec_of_surjective` makes `Spec.map ψ` a closed immersion.
Cancelling the isomorphism `(coordinateIso V).hom.left` gives the claim.

## The ordered product

- `list_prod_ofFn_eq_of_ne`: in a monoid, the ordered product of `f : Fin r → M`
  equals `f j` when `f i = 1` for every `i ≠ j`. The proof is by induction on `r`.
- `scalarPoint_zero`: the scalar point `0` is the identity.
  `scalarPoint_affine`: on an affine test, a scalar point is the affine point of
  its parameter.
- `point_single` and `point_zero`: `point y T (Pi.single j c)` is the image of
  the scalar point `c` under `y j`, and `point y T 0 = 1`.
- `act_point`: from `hy`, `b.act s (point y T c)` equals `point y T` of the
  coordinates `charValue (w i) T s * c i`. Here `b.act s` is a monoid
  homomorphism on points (`b.pointAut`), so it commutes with the list product
  (`map_list_prod`).
- `morphism_isPointedEquivariant`: `morphism y` is pointed equivariant from
  `PointedAction.ofGroup (diagonalAction w)` to `PointedAction.ofGroup b`.
  Equivariance follows from `comp_morphism`, `act_point` and
  `coordinates_diagonalPointAction`. The origin is preserved by `point_zero`.
- `factor_isPointedEquivariant`: each `y j` is pointed equivariant from the
  diagonal action of `Ga` with the single weight `w j` to
  `PointedAction.ofGroup b`. Equivariance follows from `hy`, since every point
  of `Ga` is a scalar point. The origin is preserved because `y j` is a
  monoid morphism.

## Assembly

- `exists_lift`: `y j` is a closed immersion and is pointed equivariant
  (`factor_isPointedEquivariant`). Clause 3 of the published
  `closedImmersionPullback` then says that the image of the weight-`w j` space
  of `b` under `pullback (y j)` is the weight-`w j` space of the diagonal action
  on `Ga`. That space contains `coordinateFunctions k 1 0`
  (`coordinateFunctions_mem_weightSpace`), which therefore has a preimage `g`
  of weight `w j`.
- `affinePoint_single_comp_morphism`: the rational point
  `affinePoint k (Pi.single j 1)` followed by `morphism y` equals the rational
  point `affinePoint k (fun _ => 1)` of `Ga` followed by `y j`. This uses
  `comp_morphism`, `scalarPoint_affine` and `point_single`.
- `pullback_lift_eq`: the published `pullback_mem_weightSpace` and
  `morphism_isPointedEquivariant` give `pullback φ g` weight `w j`. So
  `eq_smul_coordinateFunctions` gives `pullback φ g = c • coordinateFunctions k r j`.
  Evaluate both sides at the rational point `affinePoint k (Pi.single j 1)`.
  The right side gives `c`. By `coordinates_comp` and
  `affinePoint_single_comp_morphism`, the left side is the value of
  `pullback (y j) g = coordinateFunctions k 1 0` at the point `1` of `Ga`, which
  is `1`. Hence `c = 1`.

## Provenance

The target is an internal proposition (see its Markdown). This proof implements
the route proposed in that Markdown. A lift of each axis coordinate exists in
the matching weight space of `G` by the closed-immersion weight-quotient result.
It pulls back to a multiple of the same linear coordinate on affine `r`-space,
because independent weights exclude every other monomial of that weight. The
scalar is fixed as `1` at a rational point on the axis. The helpers in this file
are routine translations between the Library's actual coordinate presentations,
`VectorGroup` points, and Mathlib's polynomial and closed-immersion API.
