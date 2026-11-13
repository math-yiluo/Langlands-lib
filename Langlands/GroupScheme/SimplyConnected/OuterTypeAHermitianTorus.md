# The split torus in the descended Hermitian presentation

Author: Worker 5375.

This internal module completes the descent step of Task 6209
(`OuterTypeAHermitianPresentationStatement`). The setting, `E`, `H`, `InnerTrivial`,
`OuterHermitian`, `descendedIso` and `matrixPoints` are those of
`OuterTypeAHermitianDescent`.

The torus is handled abstractly:
- `Y` is any scheme over `Spec K` and `incl : Y ⟶ G.X` is any morphism;
- `ch : Fin (n + 1) → (Y ⟶ 𝔾_m.X)` is any family of morphisms.

For the actual data of the target statement, take `Y = d.splitTorus.X`,
`incl = d.splitInclusion.hom.hom` and `ch i = (CommGroupScheme.groupHom (χ i)).hom.hom`.
Write `χ_i(s) = Gm.pointsEquiv _ T (s ≫ ch i)`, a unit of `Γ(T)`.

## Hypothesis

`TorusDiagonal E incl ch` states the following. For every test scheme `Z`, cover point
`a : Z ⟶ Spec M` and point `s : Z ⟶ Y`, the `SL_(n+1)` matrix of
`(E.toFun a)⁻¹ (s ≫ incl)` is the diagonal matrix of the `χ_i(s)`. With the actual data,
this is exactly the torus clause of the published `SpecialLinearTitsCocycleStatement`.

## Relations among the torus units

At cover points:
- `prod_cover`: `∏ χ_i(s) = 1`, by taking determinants.
- `exists_moves`: some `σ ∈ Aut_K(M)` moves an element of `L`, namely a lift of the
  conjugation of `L` (Mathlib's `AlgEquiv.liftNormal`). This uses `IsGalois K M`.
- `mul_cover`: if `H i j ≠ 0`, then `χ_i(s) χ_j(s) = 1`. Write `D` for the diagonal
  matrix of the `χ_i(s)` and `g` for the corresponding element of `SL_(n+1)`.
  - By `TorusDiagonal` at `a` and at `a ≫ coverAut K M σ`, both inverse images of `s ≫ incl` are
    the same `D`, so the discrepancy of `g` at `σ` is `g` itself.
  - `OuterHermitian` then gives `D = X D⁻¹ X⁻¹`, with `X` the coefficient image of `H⁻¹`.
  - Comparing `(i, j)` entries gives `u_i Y_ij u_j = Y_ij`, where `Y = X⁻¹` is the
    coefficient image of `H` and `u_i = χ_i(s)`. The entry `Y_ij` is the image of the
    nonzero field element `H i j`, hence a unit.

On every test scheme `T`:
- `cancel_fst K M`: morphisms out of `T` are determined after composing with the
  projection `T ×_K Spec M → T`. This projection is an effective epimorphism, because
  `Spec M → Spec K` is fpqc (the published `fieldExtension_fpqc`).
- `unitsMap_fst_injective`: pulling units back along this projection is injective.
  `unitsMap_fst_pointsEquiv` identifies the pulled-back units with the units of the
  pulled-back points.
- `prod_eq_one` and `mul_eq_one` transfer the two cover relations to every `T`, using the
  second projection as a cover point.

## The diagonal torus matrix

- `scalarSections L T : Γ(T) →+* L ⊗_K Γ(T)` is `r ↦ 1 ⊗ r`.
  - `scalarSections_bar`: it is fixed by the tensor conjugation.
  - `firstCoord_scalarSections`: its first coordinate is `r`.
  - `tensorMap_scalarSections`: it is natural in the test scheme.
- `torusMatrix L ch T s` is the diagonal matrix with entries `1 ⊗ χ_i(s)`.
  - `torusMatrix_det`: its determinant is `1`.
  - `torusMatrix_preserves`: it preserves the extended form of `H`. Each `(i, j)` entry
    of `Dᴴ H D` is `H_ij ⊗ χ_i(s) χ_j(s)`, and either `H_ij = 0` or the product of units
    is `1`.
  - `torusTensorPoint` packages it as a point of `SchemeModel.tensorPoints K L H T`.

## Results

- `matrixPoints_torus`: under `InnerTrivial`, `OuterHermitian` and `TorusDiagonal`,
  `matrixPoints K L H (descendedIso L H E hin hout) T (s ≫ incl) = torusMatrix L ch T s`
  for every test scheme `T` and every `s : T ⟶ Y`.
  - The proof shows `s ≫ incl = δ ≫ descendedIso.hom`, where `δ` is the point of `SU(H)`
    with matrix `torusMatrix`.
  - Both sides are compared after pulling back to `T ×_K Spec M`. There
    `comp_descendedIso_hom` evaluates the right side through `E` at the second projection,
    and `TorusDiagonal` identifies the result.
- `exists_hermitianPresentation`: under the same three hypotheses there is a family `ρ`,
  namely `matrixPoints K L H (descendedIso L H E hin hout)`, with four properties:
  - it is injective on every test scheme;
  - its image is exactly the determinant-one isometries of `H` over `L ⊗_K Γ(T)`;
  - it is natural in the test scheme;
  - it sends `s ≫ incl` to the diagonal matrix with entries `1 ⊗ χ_i(s)`.

  These four conjuncts have the shape of clauses 3 to 6 of the conclusion of
  `OuterTypeAHermitianPresentationStatement`, with `J = H.gram`, written via
  `Algebra.TensorProduct.includeRight` as in the target.

## Provenance and scope

The provenance is internal. The argument is the standard observation that a split torus
of `SL_(n+1)` that descends to a unitary group sits diagonally in it. Each character
`χ_i` pairs with `χ_j` through a nonzero Gram entry `H_ij` of the descended form. The
module does not produce `E`, `H`, the characters or the hypotheses. It does not prove the
star-action, Hermitian-symmetry or root-restriction clauses of the target statement.
