# Lifts of the reflection of a quaternionic line to a spin cover

Module `Langlands.GroupScheme.Rational.QuaternionicSpinLineReflection`, namespace
`Langlands.GroupScheme`.

## Main result

`lineReflection_lift_mul_self_ne_one`. Let `F` be a field of characteristic zero, `D` a
central division `F`-algebra with `dim_F D = 4`, `σ` a first-kind involution of `D` whose
symmetric subspace has dimension `3`, `n ≥ 3` and `q : σ.QuadraticForms (Fin n)`
nondegenerate. Let `p : G ⟶ σ.normOneIsometryGroup q` be a central isogeny from a simply
connected group scheme `G`. Let `x ∈ Dⁿ` with `c = h(x, x) ≠ 0`, let `Ω` be an algebraically
closed field over `F`, and let `y` be an affine `Ω`-point of `G` whose image under `p` has
tensor unit `1 ⊗ lineReflection σ q x` in `Ω ⊗ M_n(D)`. So `p(y)` is the negation of the
line `D x`, fixing its orthogonal complement. Then `y * y ≠ 1`.

Classically: in the spin group, a lift of the rotation by `π` of a nondegenerate plane has
order four. The negation of a quaternionic line becomes such a rotation after splitting `D`.

## Auxiliary results

* `Lie.affineBaseChangeEquiv_comp`: the affine base-change comparison
  `Lie.affineBaseChangeEquiv k K _ A` commutes with composition with a homomorphism
  `f : G ⟶ H` of group schemes (from
  `GaloisCocharacterDescent.baseChangePointsEquiv_morphism`).
* `CliffordSpin.toLinearMap_matrixAction`: the matrix action of `g ∈ GL_N(A)` on `A ⊗ V` is
  the linear map of `g` in the base-changed basis.
* `CliffordSpin.finrank_range_matrixAction_sub_id`: the range of `matrixAction g - id` has
  dimension `rank(g - 1)`.

## Proof of `lineReflection_lift_mul_self_ne_one`

Suppose `y * y = 1`.

1. **Splitting and the Clifford model.** Over `Ω` choose a splitting
   `e : Ω ⊗ D ≃ M₂(Ω)` (`CentralSimple.exists_matrix_chart_reducedDegree`, reindexed by
   `reducedDegree_eq_two`). Let `Q = NormOneSplit.gramQ e σ q`, nondegenerate by
   `MoritaIsometry.isNondegenerateQuadratic_gramN`. The base change of `p` followed by
   `NormOneSplit.splitIso` is a central isogeny `r` from the simply connected group `G_Ω`
   (`isSimplyConnectedFieldExtension`) onto `(scalar Ω).normOneIsometryGroup Q`. Then:
   `ordinaryOrthogonalGeometry` and `scalarConnectedIsometryIso_normOne` show that the target
   is semisimple; `natCard_scalarEvenSpinKernel` with `kernelSquareIso` shows that `kernel r`
   has two geometric points; and `CliffordSpin.exists_iso_of_simplyConnected_scalarCover`
   gives an isomorphism `c` from `G_Ω` to the Clifford lift group of `Q` compatible with the
   projections.
2. **The split matrix.** Let `y''` be `y` moved to `G_Ω`. By
   `Lie.affineBaseChangeEquiv_comp`, its image under the base change of `p` is the moved
   image of `y`. By `scalarMatrixPoint_splitIso` (module `Quaternionic/NormOneSplitAffine`)
   the scalar matrix point of its image under `r` is
   `γ = chartN e n Ω (1 ⊗ lineReflection σ q x)`. Since
   `1 ⊗ lineReflection = lineRotationMatrix (-1)` (`map_lineReflection`), we get `γ² = 1`
   (`lineRotationMatrix_mul`, `lineRotationMatrix_one`), `γ ≠ 1`
   (`lineRotationMatrix_neg_one_ne_one` and injectivity of the charts), and
   `rank(γ - 1) ≤ 2` (`rank_chartN_lineRotationMatrix_sub_one`).
3. **The Clifford unit.** Let `xP = c(y'')`, a point of the Clifford lift group, and
   `pr = CliffordSpin.affinePairEquiv` of it. Its matrix component is the inverse transpose
   of the scalar matrix point of `r(y'')` (`CliffordSpin.actionMatrix_projection`), hence
   `γᵀ` because `γ² = 1`. The corresponding spin lift `sL = coefficientLiftEquiv pr` acts
   on vectors by `matrixAction pr.2` (`CliffordSpin.vectorAction_coefficientLiftEquiv`). So
   its vector action is an involution, not the identity, and moves vectors only inside a
   subspace of dimension `rank(γᵀ - 1) = rank(γ - 1) ≤ 2`
   (`finrank_range_matrixAction_sub_id`, `Matrix.rank_transpose`). By
   `CliffordSpinLift.unit_mul_unit_eq_neg_one_of_involution` (module
   `LinearAlgebra/CliffordPlaneInvolution`, with nondegeneracy from
   `CliffordSpin.nondegenerate_polar_baseChange`) its Clifford unit squares to `-1`.
4. **Contradiction.** `y * y = 1` gives `y'' * y'' = 1`, hence `xP * xP = 1`, `pr * pr = 1`,
   `sL * sL = 1`, and the Clifford unit squares to `1`, since all comparison maps are
   multiplicative. So `1 = -1` in the Clifford algebra, and `2 = 0` in `Ω` because
   `algebraMap Ω (CliffordAlgebra _)` is injective. This contradicts characteristic zero.

## Provenance

The underlying fact is the structure of the spin double cover of a split orthogonal group.
The proof is derived from the Library's Morita splitting of quaternionic norm-one groups and
its Clifford comparison of simply connected scalar covers, as listed above.
