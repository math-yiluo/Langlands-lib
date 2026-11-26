# Connectedness of quaternionic norm-one isometry groups

Module: `Langlands.GroupScheme.Quaternionic.NormOneIsometryConnectedness`.

The module states `Langlands.GroupScheme.QuaternionicNormOneIsometryConnectednessStatement`
and proves it at every universe as `Langlands.GroupScheme.quaternionicNormOneIsometryConnectedness`.
The statement says: over a field `K` of characteristic zero, for a central division algebra
`D` with `dim_K D = 4`, an involution of the first kind `σ` with `dim_K D^σ = 3`, a positive
rank `m` and a quadratic form `q : σ.QuadraticForms (Fin m)` in the sense of Tits whose polar
Gram matrix is invertible, the underlying topological space of the scheme
`(σ.normOneIsometryGroup q).X.left` is connected. Here `σ.normOneIsometryGroup q` is the
kernel of the reduced norm of `M_m(D)` on the isometry group scheme `O(q)`, the special
unitary group of the corresponding skew-hermitian form.

## Splitting

The declarations of the namespace `Langlands.GroupScheme.Quaternionic.NormOneSplit` work with
any field `L` over `K` and any chart `e : L ⊗[K] D ≃ₐ[L] M_2(L)`. They use the matrix chart
`MoritaIsometry.chartN e m R : R ⊗[K] M_m(D) ≃+* M_{2m}(R)` and the split Gram matrix
`C = MoritaIsometry.gramN e σ m Q₀` of a representative `Q₀ = Quotient.out q`, both from
`QuaternionicMoritaIsometryProof`. `gramQ e σ q` is the scalar quadratic form over `L`
represented by `C`.

- `baseChangeNormOne σ q` is the base change of `σ.normOneIsometryGroup q` to `Spec L`.
- `unitPoint σ q T x` is the unit of `Γ(T, ⊤) ⊗[K] M_m(D)` underlying a point `x` over a
  scheme `T` over `Spec L`. It is obtained through the pullback adjunction
  (`GroupScheme.baseChangePointsEquiv`), the ambient inclusion `normOneIsometryAmbientι` and
  `FiniteAlgebraUnits.pointsEquiv`. `unitPoint_injective` holds because the ambient inclusion
  is a monomorphism.
- `matrixPoint e σ q T x` is the invertible matrix `chartN (unitPoint x)` over `Γ(T, ⊤)`.
  `matrixPoint_injective` follows from injectivity of the chart, and
  `matrixPoint_naturality` from `chartN_naturality`: pullback along `T' ⟶ T` applies the
  section map to every entry.
- `det_chartN`: the determinant of `chartN x` is the reduced norm of `x`
  (`reducedNorm_eq_det_matrixChartR`, since reindexing does not change determinants).
- `mem_range_matrixPoint_iff` (with `dim_K D^σ = 3`): an invertible matrix `g` over
  `Γ(T, ⊤)` is the matrix of a point exactly when `g C gᵀ - C` is alternating and
  `det g = 1`. The isometry condition is translated by `MoritaIsometry.mem_isometryUnits_iff`,
  and the norm condition by `det_chartN`. In the converse direction the unit
  `chartN⁻¹(g)` satisfies the tensor equations of
  `mem_range_normOneIsometryAmbientι_iff_equations`, so it is the image of a point of the
  norm-one group over the restricted test, and the pullback adjunction gives the point of the
  base change.
- `range_matrixPoint_eq` compares this image with the image of the scalar chart
  `ScalarNormOnePoints.matrix (gramQ e σ q) T`, which `ScalarNormOnePoints.mem_range_matrix_iff`
  describes by the same two equations.
- `splitPointsEquiv` is the resulting multiplicative bijection from points of the base
  change to points of `(scalar L).normOneIsometryGroup (gramQ e σ q)` with the same matrix
  (`matrix_splitPointsEquiv`). It is natural in the test scheme
  (`splitPointsEquiv_naturality`), so `isoOfPoints` gives the isomorphism of group schemes
  `splitIso`.

## Connectedness

`connectedSpace_normOneIsometryGroup` assumes characteristic zero and nondegeneracy of `q`.
The split form is nondegenerate (`MoritaIsometry.isNondegenerateQuadratic_gramN`), `L` has
characteristic zero, and `2` is invertible in `L`. So the scalar norm-one group is connected
(`CliffordSpin.connectedSpace_scalarNormOne`). The isomorphism `splitIso` carries this to the
base change (`DynamicConnected.connectedSpace_of_iso`). The map `Spec L → Spec K` is
surjective (`fieldExtension_fpqc`), so connectedness descends
(`connectedSpace_of_baseChange`). The final theorem takes `L` to be the Library's finite
Galois splitting field `CentralSimple.finiteGaloisSplittingField K D`, with its chart
reindexed to `2 × 2` matrices by `FirstKindInvolution.reducedDegree_eq_two`.

This is the splitting of skew-hermitian forms over a quaternion algebra into quadratic forms
of dimension `2m` used by Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969),
§2.6, proof of Lemma 2, printed p. 33 (PDF p. 39). The module follows the construction of the
splitting isomorphism of the quaternionic symplectic groups in `SymplecticReductive`.
