# Lie coordinates and the diagonal torus of the split special linear group

This internal module builds the coordinates needed to compute the roots of the split special
linear group `SpecialLinear.groupScheme n R` (from `Langlands.GroupScheme.Reductive.SpecialLinear`)
for a finite index type `n` with decidable equality. It has three parts:

- matrix coordinates on the Lie algebra, identifying it with the trace-zero matrices;
- a diagonal torus of rank `|n| - 1`, normalized by a chosen *pivot* index `p : n`;
- the weight-space decomposition of the Lie algebra under that torus over a field.

The pivot is needed because the determinant condition removes one coordinate: the torus has
coordinates indexed by `OffPivot p = {c : n // c ≠ p}`, and its pivot entry is the inverse of
the product of the others. The module
`Langlands.GroupScheme.SpecialLinearSimplyConnected` uses these coordinates to show that
`SL_n` over a field is simply connected.

## Dual-number determinant-one matrices

Here `GeneralLinear.DualNumber.epsilonMatrix Y` is the matrix `εY` over the dual numbers
`A[ε]`, from the Library's `GL_n` Lie algebra coordinates.

* `det_one_add_epsilonMatrix`: `det (1 + εY) = 1 + ε tr Y`. It follows from Mathlib's
  `Matrix.det_one_add_smul` and `ε² = 0`.
* `epsilonMatrix_eq_zero_iff`: `εY = 0` exactly when `Y = 0`.
* `one_add_epsilonMatrix_det_eq_one_iff`: `1 + εY` has determinant one exactly when
  `tr Y = 0`.

## Lie coordinates

Let `R` be a commutative ring and `A` an `R`-algebra.

* `affinePointsEquiv_inclusion`: on affine points, the inclusion `SpecialLinear.inclusion n R`
  of `SL_n` into `GL_n` is `Matrix.SpecialLinearGroup.toGL`.
* `lieMatrix` (definition): the `A`-linear map from the Lie algebra
  `Additive (lieKernel (groupScheme n R) A)` of `SL_n` to `Matrix n n A`. It is the Lie map of
  the inclusion into `GL_n` (`Lie.targetMapLinear`) followed by the inverse of the Library's
  `GL_n` coordinate equivalence `GeneralLinear.DualNumber.pointKernelLinearEquiv`.
  `pointKernelLinearEquiv_lieMatrix` records that relation.
* `mono_inclusion` (instance): the inclusion of `SL_n` into `GL_n` is a monomorphism of
  schemes.
* `lieMatrix_injective`: `lieMatrix` is injective.
* `affinePointsEquiv_lieKernel`: the dual-number point of `SL_n` underlying a Lie algebra
  element `X`, read in `SL_n(A[ε])` through `SpecialLinear.affinePointsEquiv`, has matrix
  `1 + ε · lieMatrix X`.
* `trace_lieMatrix`: every `lieMatrix X` has trace zero, by
  `one_add_epsilonMatrix_det_eq_one_iff`.
* `exists_lieMatrix_eq`: every trace-zero matrix `Y` is `lieMatrix X` for some Lie algebra
  element `X`.

So `lieMatrix` is a linear isomorphism from the Lie algebra of `SL_n` onto the trace-zero
matrices. The module does not package this as a single equivalence.

## Weights of the diagonal torus

Fix a pivot `p : n`.

* `OffPivot p` (abbreviation): the subtype `{c : n // c ≠ p}`.
* `weightCoord p x : OffPivot p → ℤ` (definition): the weight of the diagonal entry `x`, in
  coordinates. It is the standard basis vector `e_x` for `x ≠ p` (`weightCoord_of_ne`,
  `weightCoord_val`) and the constant `-1`, that is `-∑_c e_c`, at the pivot
  (`weightCoord_pivot`).
* `weightCoord_apply_mem`: every weight coordinate is `-1`, `0` or `1`.
* `sum_weightCoord`: the weights of all entries sum to zero.
* `weightCoord_injective`: distinct entries have distinct weights.
* `torusWeights p τ x : Aˣ` (definition): for torus coordinates
  `τ : ULift (OffPivot p) → Aˣ`, the product `∏_c τ_c ^ (weightCoord p x)_c`. It is `τ_x` for
  `x ≠ p` (`torusWeights_val`) and `(∏_c τ_c)⁻¹` at the pivot (`torusWeights_pivot`). The entries
  multiply to one (`prod_torusWeights`). They are multiplicative in `τ` (`torusWeights_mul`,
  `torusWeights_one`) and natural in ring maps (`map_torusWeights`).
  `torusWeights_mulSingle` evaluates them on `Pi.mulSingle c U`.
  `prod_zpow_weightCoord_sub` writes `τ^(w(x) - w(y))` as `torusWeights τ x · (torusWeights τ y)⁻¹`.
* `torusUnits p A` (definition): the group homomorphism `(ULift (OffPivot p) → Aˣ) →* SL_n(A)`
  sending `τ` to the diagonal matrix `diag(torusWeights p τ)`. `coe_torusUnits` gives its
  matrix; `toGL_torusUnits` identifies its image in `GL_n` with the Library's
  `GeneralLinear.diagonalTorusUnits`; `map_torusUnits` is naturality in ring maps.

The `ULift` matches the index type of the Library's split torus
`splitTorus (Spec R) (ULift (OffPivot p))`, which lives in the universe of `R`.

## The diagonal torus

* `diagonalTorusPoints p R T` (definition): on points over a test scheme `T`, the group
  homomorphism from points of `splitTorus (Spec R) (ULift (OffPivot p))` to points of `SL_n`.
  It is `torusUnits` transported along `splitTorus.pointsEquiv` and
  `SpecialLinear.pointsEquiv` (`pointsEquiv_diagonalTorusPoints`). It is natural in `T`
  (`diagonalTorusPoints_naturality`).
* `diagonalTorus p R` (definition): the resulting morphism of group schemes
  `(splitTorus.commGroupScheme (Spec R) (ULift (OffPivot p))).toGrp ⟶ groupScheme n R`,
  obtained from the Library's `homOfPoints`. On points it sends `(τ_c)` to
  `diag(torusWeights p τ)`, i.e. `τ_c` at `c ≠ p` and `(∏_c τ_c)⁻¹` at the pivot
  (`pointsEquiv_diagonalTorus`).
* `mono_diagonalTorus_hom` (instance): the diagonal torus is a monomorphism, since the
  off-pivot diagonal entries recover the coordinates.
* `affinePointsEquiv_diagonalTorus_inclusion`: on affine points, the composite with the
  inclusion into `GL_n` is `GeneralLinear.diagonalTorusUnits` of the weights `torusWeights`.

## Weight spaces over a field

Let `k` be a field and `𝔻` the split torus
`splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (OffPivot p))`.

* Instances `isAffineHom_groupScheme_of`, `smooth_groupScheme_of` and
  `connectedSpace_groupScheme_of` restate the Library's results `isAffineHom_groupScheme`,
  `smooth_groupScheme` and `connectedSpace_groupScheme` for the base `CommRingCat.of k`. The last
  two assume `[Nonempty n]` and use `Classical.arbitrary n` as the pivot that those published
  results take. `isAffineHom_diagonalTorusSource` is the affineness of `𝔻` itself.
* `isSplitTorus_diagonalTorus n p k`: `𝔻` is a split torus.
* `isClosedSubgroup_diagonalTorus n p k`: the diagonal torus is a closed subgroup. This uses
  the Library's `IsTorus.isClosedSubgroup_of_mono` and `mono_diagonalTorus_hom`.
* `isSplitSubtorus_diagonalTorus`: the two facts together.
* `characterValue_eq_prod`: a character `χ` of `𝔻` takes the value
  `∏_c τ_c ^ χ_c` on a point with coordinates `τ`. Here `χ_c` are the coordinates
  `GeneralLinear.characterCoordEquiv (OffPivot p) k χ`.
* `mem_weightSpace_diagonalTorus_iff`: membership of a Lie algebra element `X` in the weight
  space of `χ` (the Library's `weightSpace (diagonalTorus p (CommRingCat.of k)) χ`), written
  entrywise. For every `k`-algebra `A` and point `t`, the conjugate
  `torusWeights(x) · X_{xy} · torusWeights(y)⁻¹` equals `χ(t) · X_{xy}`. The proof transports
  weight spaces along the inclusion into `GL_n`
  (`lieKernelHomLinear_mem_weightSpace_iff`) and uses the Library's `GL_n` adjoint formula.
* `mem_weightSpace_diagonalTorus_iff_support` (**weights of the diagonal torus**): `X` lies in
  the weight space of `χ` exactly when every nonzero entry `X_{xy}` has
  `χ = w(x) - w(y)`, where `w = weightCoord p`. For the forward direction, evaluate at the
  Laurent-polynomial point `Pi.mulSingle c T` and compare exponents with the Library's
  `GeneralLinear.exponent_eq_of_C_mul_T`.

## Provenance

The module is internal: it supplies coordinates for proving a standard fact. The diagonal
maximal torus of `SL_n` and its roots `e_x - e_y` (relative to the full diagonal torus of
`GL_n`) are standard; see Milne, *Algebraic Groups* (2017), where `SL_n` is simply connected
(Example 23.61, printed p. 502). The pivot normalization, which writes the rank `|n| - 1`
torus with coordinates `OffPivot p`, is an implementation choice of this module. The Lie
algebra coordinates reduce to the Library's dual-number coordinates for `GL_n`.
