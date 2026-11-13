# Split orthogonal coordinates adapted to the quaternionic Levi torus

Authors: Worker 146.

This internal helper unit supports the proof of
`Langlands.GroupScheme.Quaternionic.SpinKernel.SpinKernelGeneratorStatement`
(Task 5870). It supplies the full orthogonal coordinates that the published reduction
`SpinKernel.kernelGenerator_of_orthogonalCoordinates` consumes.

Setting:

- `D` is a finite-dimensional division algebra over a field `K`, and `σ` is an
  involution of the first kind whose symmetric subspace has dimension `3`.
- `q` is a nondegenerate `σ`-quadratic form on `D^m`, with `m > 0` and a hyperbolic
  pair `h : σ.IsHyperbolicPair q v w`.
- `L` is an algebraically closed field over `K` with a matrix chart
  `e : L ⊗[K] D ≃ₐ[L] M₂(L)`.

The base change of the isometry group `O(q)` to `L` is identified with the split
orthogonal group `OrthogonalMatrix.groupScheme (Fin m) L`. The identification is chosen
so that the hyperbolic Levi torus of `h` becomes the first diagonal coordinate of the
standard torus. The quaternionic Morita comparison (`MoritaIsometry.splitIso`) is not
enough for this, since its split Gram matrix is in arbitrary position. This proof
constructs the prescribed adapted coordinates directly from the explicit image of
the Levi torus.

The unit cites no outside source. It is derived from the Library's Morita chart
(`MoritaIsometry.chartN`, `gramN`, `basePointsEquiv`, `mem_isometryUnits_iff`,
`isNondegenerateQuadratic_gramN`), the hyperbolic extension
(`HyperbolicScheme.extendUnits`, `extendUnits_preserves`), the Levi matrix
(`LeviScheme.leviMatrix_isometry`), the splitting comparisons of
`OrthogonalMatrix.Comparison`, and the linear algebra of
`Langlands.GroupScheme.OrthogonalMatrix.AdaptedHyperbolic`.

## The weight vectors

`constChart e d = e (1 ⊗ d)` is the chart on constants, a `K`-algebra map
`D → M₂(L)`. Write `Ret` and `Inc` for the retraction `planeRetraction σ q v w` and the
inclusion `planeInclusion v w` of the hyperbolic plane. Write `S` for
`σ.involutionMatrix e`, so that `e(σ y) = S e(y)ᵀ S⁻¹`. The four vectors, indexed by
`Fin m × Fin 2` and read in `Fin (2 * m)` through `blockIndex` (`blockVec`), are:

- `col₁ (i, a) = e(Ret i 0) a 0`;
- `row₁ (j, c) = e(Inc 0 j) 0 c`;
- `col₂ (i, a) = (e(Ret i 1) S) a 0`;
- `row₂ (j, c) = (S⁻¹ e(Inc 1 j)) 0 c`.

`planeChart_mul` maps `Inc * Ret = 1` (`h.planeInclusion_mul_retraction`) through
`constChart`. With the block-sum identity `block_sum`, it gives the four dot products
`row₁_col₁ = 1`, `row₁_col₂ = 0`, `row₂_col₁ = 0` and `row₂_col₂ = 1`.

## The chart of the extended Levi matrix

The setting here is a commutative `L`-algebra `R` with `IsScalarTower K L R`.

- `coefficientEquiv_eq_equiv`: the two tensor/matrix comparisons agree.
- `chartN_equiv_symm_apply`: the Morita chart of a matrix over `R ⊗ D` is the block
  matrix of the charts `chartR e R` of its entries.
- `extendUnits_hyperbolicLevi_apply`: the entries of
  `extendUnits h R (hyperbolicLevi b)` are `1 + Ret i 0 (b - 1) Inc 0 j +
  Ret i 1 (σ(b⁻¹) - 1) Inc 1 j`.
- `chartR_inv_of_eq` and `mul_single_mul_apply` are small helpers.
- `chartN_extendUnits_hyperbolicLevi`: if `chartR e R b = diag(s, 1)`, then the chart of
  `extendUnits h R (hyperbolicLevi b)` is `weightMatrix` of the four vectors (mapped
  to `R`), with parameters `s` and `s⁻¹`. That is,
  `1 + (s - 1) col₁ row₁ + (s⁻¹ - 1) col₂ row₂`.

## Invariance and the adapted coordinates

- `extendUnits_levi_mem`: over any `K`-algebra `R`, the extended Levi matrix of any
  unit is an isometry unit of the split representative `Q₀` of `q`. This combines
  `extendUnits_preserves` and `leviMatrix_isometry` through
  `TensorMatrix.mem_alternating_iff`.
- `isAlt_weightMatrix_gramN`: for every `s : Lˣ`, the weight matrix with parameters
  `s, s⁻¹` preserves the split Gram matrix `gramN e σ m Q₀`. Apply the previous lemma
  to `b = chartR⁻¹ (diag(s, 1))` (`diagUnit`) over `R = L`, then
  `mem_isometryUnits_iff` and `chartN_extendUnits_hyperbolicLevi`.

## The isomorphism

Fix `P`, `P'` with `P * P' = 1`, `P' * P = 1` and
`P * gramN * Pᵀ - formMatrix` alternating.

- `splitModelHom` sends the Morita point model (`splitModel`) to orthogonal matrices,
  `u ↦ P U P'`, through `OrthogonalMatrix.splitMatrix`. It is bijective
  (`splitModelHom_bijective`).
- `adaptedPointsEquiv` composes it with `MoritaIsometry.basePointsEquiv`. Restriction
  along test maps commutes with it (`adaptedPointsEquiv_naturality`).
- `adaptedIso` is the resulting isomorphism, built with `isoOfPointModels`.
  `pointsEquiv_adaptedIso` reads its points.

## Main result

`exists_adaptedCoordinates`. Let `L` be algebraically closed and `0 < m`, with `q`
nondegenerate and `h` a hyperbolic pair. Then there is an isomorphism

`Φ : (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q) ≅
OrthogonalMatrix.groupScheme (Fin m) (CommRingCat.of L)`

with the following property. Take a test scheme `U` over `Spec L`, a point `x` of the
base change, a unit `b` of `R ⊗[K] D` and a unit `s` of `R`, where
`R = restrictedSections K L U`. Suppose `chartR e R b = diag(s, 1)`, and suppose the
matrix of `x` (through `GroupScheme.baseChangePointsEquiv` and
`HyperbolicScheme.matrixPointsEquiv`) is `extendUnits h R (hyperbolicLevi b)`. Then
the orthogonal matrix of `x ≫ Φ.hom` is the Levi matrix of
`diagonalTorusUnits (Pi.mulSingle ⟨0, hm⟩ s)`, that is
`diag(s, 1, …, 1, s⁻¹, 1, …, 1)`.

Proof.

1. `Q₀` is the split representative, so `gramN + gramNᵀ` is invertible by
   `isNondegenerateQuadratic_gramN`.
2. Choose `s₀ ∉ {0, 1, -1}` (`L` is infinite).
3. Apply `exists_weight_adapted_matrix` with the four vectors, the dot products above
   and `isAlt_weightMatrix_gramN s₀`. This gives `P`, `P'`. Take `Φ = adaptedIso`.
4. For a point as in the hypothesis, its Morita chart equals the weight matrix with
   parameters `s, s⁻¹`. This uses `scalarChart_theta` and
   `chartN_extendUnits_hyperbolicLevi`.
5. `conj_weightMatrix` (with `map_conj_single`) turns `P (weight matrix) P'` into
   `1 + single (inl 0) (inl 0) (s - 1) + single (inr 0) (inr 0) (s⁻¹ - 1)`.
6. `one_add_single_eq_levi` identifies this with the Levi matrix of the diagonal torus
   element.

The conclusion has exactly the form used to build the cocharacter comparison `ha` that
`SpinKernel.kernelGenerator_of_orthogonalCoordinates` takes as input.
