# The binary group `SL₂ × SL₁(D)` inside the Hermitian model `SU₄`

This module builds a morphism of group schemes over a field `K`

```
QuatData.binaryHom : BinaryScheme.groupScheme ⟶ HermitianRoot.SchemeModel.groupScheme K L H w hw
```

from the published binary group `SL₂ × SL₁(D)` (`Quaternionic.BinaryScheme.groupScheme`) to the
published special unitary group scheme of a diagonal Hermitian form over the quadratic field
`L = K[X]/(X² - c)` (`HermitianRoot.SchemeModel.groupScheme`). It also proves the explicit formula
for the morphism on the points of every test scheme. Everything is in the namespace
`Langlands.GroupScheme.KneserThree`. The construction is the binary part of Kneser's
identification of a group of type `A₃` with one of type `D₃`, used for the
`KneserThreeSpinSubgroupStatement` step of Task 5398. The unit was requested by Worker 14, who
calls it (U6).

## Setting

`Q : QuatData K D` is the published splitting data of `KneserThreeSplitting`. It consists of
elements `x, j` of the `K`-algebra `D` with `x² = c`, `j² = δ`, `jx = -xj`, a basis
`1, x, j, jx`, the quadratic field `L = field Q.c` (irreducible and separable over `K`), and the
embedding `ι : L → D` sending the root to `x`. For every commutative `K`-algebra `R`, the
published `Q.presentation R` writes `R ⊗[K] D = ι(L ⊗ R) ⊕ j ι(L ⊗ R)`. Its coordinates are
`fst, snd`, its involution `c` is the tensor conjugation of `L ⊗[K] R`, and its scalar is
`δ ⊗ 1`.

The scheme part assumes that `D` is a division ring, finite-dimensional and central over `K`. These
are the hypotheses of `BinaryScheme.groupScheme`. The remaining data are:

- `H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution K L) (Fin 2)` with
  `hH : H.weight = ![-1, algebraMap K L Q.δ]`;
- unit witnesses `w : Fin 2 → Lˣ` with `hw : ∀ i, (w i : L) = H.weight i`. These are needed only
  to form the model group scheme;
- `θ θinv : L` with `hθ : SU3Root.conjugation K L θ = -θ` and `hθinv : θ * θinv = 1`.
  For example, `θ` can be the root of `X² - c`, whose conjugate is its negative by
  `QuadField.conjugation_root`.

The Library's model uses the Gram matrix `gram H` on `Index (Fin 2) = Unit ⊕ (Fin 2 ⊕ Unit)`. It
is hyperbolic on the top and bottom indices and `-diag(H.weight) = diag(1, -δ)` on the middle.
In the coordinate order `(top, m₀, m₁, bot)`, given by `fourIndexEquiv : Fin 4 ≃ Index (Fin 2)`,
this is the matrix `Presentation.gram` of `KneserThreeCore` (lemma `gram_tensorForm`).

## The presentation norm and the binary matrix (namespace `Presentation`)

These results hold for any `P : Presentation A B`.

- `norm b = fst b · bar (fst b) - δ · snd b · bar (snd b)`, and `det_rep : det (rep b) = norm b`.
- `binary θ θinv g b` (from `KneserThreeCore`) places `g` on `(top, bot)`, twisted to
  `[[g₀₀, g₀₁ θinv], [θ g₁₀, g₁₁]]`, and `rep b` on `(m₀, m₁)`.
  - `binary_one` and `binary_mul` (for `θ θinv = 1`) show it is multiplicative.
  - `det_binary`: its determinant is `det g · norm b`.
  - `isSpecialUnitary_binary`: assume `bar θ = -θ`, `θ θinv = 1`, that every entry of `g` is fixed
    by `bar`, `det g = 1` and `norm b = 1`. Then `binary θ θinv g b` preserves `gram` and has
    determinant one.
  - `bar_inv` gives `bar θinv = -θinv` from the first two of these hypotheses.

## The reduced norm in the presentation (sections `FieldPresentation`, `Chart`)

- `fieldPresentation : Presentation L D` presents `D` itself over `L`, with the conjugation of `L`
  and `δ`.
- `repAlgHom : D →ₐ[K] M₂(L)` is its matrix representation
  `ι a + j ι a' ↦ [[a, δ ā'], [a', ā]]`.
- `chartHom : L ⊗[K] D →ₐ[L] M₂(L)` sends `l ⊗ d` to `l · rep d`.
- `chartHom_bijective`: `L ⊗[K] D` is simple (`CentralSimple.isSimpleRing_baseChange`), so the map
  is injective. Both sides have dimension `4` over `L`, so it is bijective.
- `chart : L ⊗[K] D ≃ₐ[L] M₂(L)` is the resulting splitting chart.
- `splittingMap_map_includeRight`: let `S = L ⊗[K] R`. The Library's extension
  `ReducedNorm.splittingMap chart S` of the chart, applied to the image of `b ∈ R ⊗[K] D` in
  `S ⊗[K] D`, is `(Q.presentation R).rep b`.
- `includeRight_reducedNorm`: the reduced norm `CentralSimple.reducedNorm K D R b`, mapped into
  `L ⊗[K] R` by `r ↦ 1 ⊗ r`, equals `(Q.presentation R).norm b`. The proof uses the published
  naturality of the reduced norm (`reducedNorm_naturality`) and its equality with the determinant in
  any splitting chart (`reducedNorm_eq_det_fintype`), together with `det_rep`. This is the
  classical formula `Nrd(a + j a') = N(a) - δ N(a')`, valid over every commutative `K`-algebra `R`.
- `presentation_norm_eq_one`: if `b` has reduced norm one, then its presentation norm is one.

## The binary matrix over `L ⊗[K] R` (section `BinaryMatrix`)

- `binaryMatrix R θ θinv g b` is
  `(Q.presentation R).binary (θ ⊗ 1) (θinv ⊗ 1) (g.map includeRight) b`. It is a `4 × 4` matrix over
  `L ⊗[K] R` for `g : Matrix (Fin 2) (Fin 2) R` and `b : R ⊗[K] D`.
- `isSpecialUnitary_binaryMatrix`: for `det g = 1` and presentation norm one, the binary matrix is
  special unitary for `Presentation.gram`.
- `binaryMatrix_one` and `binaryMatrix_mul` show it is multiplicative.
- `binaryMatrix_map`: for every `K`-algebra map `φ : R → R'`, it is natural with respect to `φ`
  on `g` and `b` and `id_L ⊗ φ` on the coefficients.
- Helpers: `presentation_fst_eq`, `presentation_snd_eq`, `presentation_δ_eq` (unfolding the published
  presentation); `fstR_mapB` and `sndR_mapB` (naturality of the coordinates); `tmul_one_mul_tmul_one`,
  `bar_tmul_one` and `bar_includeRight`.

## The concrete points (section `Scheme`)

Let `T` be a test scheme over `Spec K` and `R = BinaryScheme.coefficients T`.

- `coefficientEquiv T : L ⊗[K] R ≃+* SpecialLinear.WeilRoot.tensorAlgebra K L T` is the identity.
  The model's coefficient ring is `L ⊗[K] R` by definition.
- `modelReindex T` sends a `Fin 4`-matrix over `L ⊗[K] R` to an `Index (Fin 2)`-matrix over the
  model's coefficients. `modelReindex_apply` gives its formula: `M ↦ M.submatrix e.symm e.symm` with
  `e = fourIndexEquiv`. It is a ring isomorphism.
- `gram_tensorForm`: the Library's Gram matrix of `tensorForm K L H T` is
  `modelReindex T (Q.presentation R).gram`. This uses `hH`.
- `conjugateTranspose_modelReindex`: conjugate transposition commutes with `modelReindex`.
- `binaryMatrixHom`: the binary matrix as a monoid homomorphism `SL₂(R) × reducedNormOne K D R →*
  M₄(L ⊗[K] R)`.
- `modelMatrixHom`: its reindexing to units.
- `modelMatrixHom_mem`: every value of `modelMatrixHom` lies in the Library's
  `specialUnitarySubgroup (tensorForm K L H T)`. This uses `isSpecialUnitary_binaryMatrix` with
  `presentation_norm_eq_one`.
- `modelPointsHom`: the resulting homomorphism into that subgroup.
- `modelMatrixHom_val` and `modelPointsHom_val` record the underlying matrices (`rfl`).

## The morphism (section `Hom`)

- `binaryPoints T`: on `T`-points, transport `modelPointsHom` through the published equivalences
  `BinaryScheme.pointsEquiv T` and `HermitianRoot.SchemeModel.pointsEquiv K L H w hw T`.
  `pointsEquiv_binaryPoints` restates this.
- `binaryPoints_naturality`: the construction is natural in `T`. It uses
  - `binaryPointsEquiv_fst_comp` and `binaryPointsEquiv_snd_comp`: naturality of the two components
    of `BinaryScheme.pointsEquiv`;
  - `HermitianRoot.SchemeModel.pointsEquiv_map`;
  - `binaryMatrix_map`.

  `tensorMap_eq_mapA` identifies the model's coefficient map along `a : T' ⟶ T` with `id_L ⊗ φ`.
- `binaryHom Q H hH w hw hθ hθinv := homOfPoints (binaryPoints …) …` is the morphism of group
  schemes.
- `binaryHom_points T x`: the matrix of `SchemeModel.pointsEquiv … T (x ≫ binaryHom.hom.hom)` is
  `modelReindex T (binaryMatrix R θ θinv g b)`, where `(g, b) = BinaryScheme.pointsEquiv T x`.
- `binaryHom_points_reindex T x`: the same statement in the coordinates `(top, m₀, m₁, bot)` over
  `L ⊗[K] R`. The model matrix, restricted along `fourIndexEquiv` and mapped by
  `(coefficientEquiv T).symm`, equals `binaryMatrix R θ θinv g b`.

Combined with `Presentation.cmap_binary` of `KneserThreeCore`, this lets the exterior-square
morphism be computed on the image of the binary group.

## Provenance

The content is internal. The embedding `SL₂ × SL₁(D) → SU₄` is the binary part of the standard
identification of `SU₄` of a Hermitian form over `L` with a spin group of type `D₃`. In that
identification, `D` is presented as `L ⊕ jL`, and `SL₁(D)` acts on the middle plane through its
matrix representation. The reduced-norm formula `Nrd(a + j a') = N(a) - δ N(a')` is classical. Here
it is proved from the Library's characterization of the reduced norm as the determinant in any
splitting chart, using the explicit chart `chart`. No literature statement is transcribed. The
published APIs used are `KneserThreePresentation`, `KneserThreeCore`, `KneserThreeSplitting`,
`BinaryQuaternionGroupScheme`, `HermitianRootGroupScheme`, `ReducedNorm`,
`ReducedNormFiniteChart` and `CentralSimpleScalarExtension`.
