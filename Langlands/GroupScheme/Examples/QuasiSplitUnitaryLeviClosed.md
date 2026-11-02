# The unitary Levi homomorphism is a closed immersion

This module proves `isClosedSubgroup_leviHom`: for fields `F` and `E` with
`Algebra.IsQuadraticExtension F E`, a finite `F`-basis `b` of
`Matrix (Fin 2) (Fin 2) E`, and any `F`-automorphism `c` of `E`, the Levi
homomorphism `leviHom b c : WeilGm.groupScheme (CommRingCat.of F) E ⟶ groupScheme b c`
is a closed subgroup. This means its underlying scheme morphism is a closed immersion. It
is the second conjunct of the Library proposition `LeviRepresentedStatement`.
The proof does not use the hypothesis `c ≠ AlgEquiv.refl`. No characteristic is excluded.

## Provenance

This is an internal helper for the proof task of `LeviRepresentedStatement`. It is not a
formalization of a cited literature passage. The definitions below are auxiliary
constructions from the Library's antidiagonal hermitian model of `U(1,1)`
(`QuasiSplitUnitary`, `QuasiSplitUnitaryLevi`) and the similitude scheme model
(`Langlands.Shimura.AlgebraInvolution`). Their content is the usual statement that the
diagonal torus of a unitary group is cut out by the vanishing of off-diagonal matrix
entries. The statement's Markdown gives the literature context (Milne, *Algebraic Groups*).

## Definitions

- `rightCoefficient l A : E ⊗[F] A →ₗ[F] A`, for a linear functional `l` on `E`, is
  `l ⊗ id` followed by `F ⊗[F] A ≅ A`. Thus `e ⊗ a ↦ l(e) • a`.
- `similitudeMatrix c A` is a group homomorphism from the similitudes of the base-changed
  involution `(involution c).baseChange A` to `GL₂(E ⊗[F] A)`. It takes the underlying unit
  in `A ⊗[F] Matrix (Fin 2) (Fin 2) E` and applies `tensorMatrixEquiv A`.
- `diagonalSimilitudes c A` is the subgroup of similitudes whose multiplier is `1` and
  whose matrix lies in the Library's block Levi subgroup for the weights `weights 1`.
  For `2 × 2` matrices this means that both off-diagonal entries vanish
  (`mem_diagonalSimilitudes`).
- `leviSimilitude c A : (E ⊗[F] A)ˣ →* similitudes` sends `a` to the Levi point
  `leviDiagonalUnitary A c a = diag(a, c_A(a)⁻¹)`. The point is viewed as a unitary element
  through `algebraPointsEquiv` and then as a similitude through `unitaryInclusion`.
- `leviSimilitudeEquiv c A : (E ⊗[F] A)ˣ ≃* diagonalSimilitudes c A` is the bijective
  corestriction of `leviSimilitude c A`.
- `universalMatrix b c` is the matrix in `Matrix (Fin 2) (Fin 2) (E ⊗[F] S)` of the
  universal similitude `(involution c).universalUnit b`, where
  `S = (involution c).similitudeCoordinateRing b`.
- `leviIdeal b c` is the ideal of `S` spanned by two kinds of elements. The first is
  `μ - 1`, where `μ` is the image of the multiplier variable. The others are the elements
  `rightCoefficient l S (universalMatrix b c i j)` for all linear functionals `l` on `E` and
  all `i ≠ j`.
- `leviCutPointsEquiv b c T` identifies the `T`-points of the Weil restriction with the
  `T`-points of the closed subgroup scheme cut out by `leviIdeal b c`. It is the composite
  of `WeilGm.pointsEquiv`, `leviSimilitudeEquiv` over the global sections of `T`, and the
  inverse of the cut-out points equivalence `Corepresented.pointsEquiv`.
- `leviIso b c : WeilGm.groupScheme (CommRingCat.of F) E ≅ cutGroupScheme _` is the
  isomorphism of group schemes obtained from these natural point bijections by
  `isoOfPoints`.

## Proof

1. Matrix calculation (`exists_leviDiagonalUnitary`). Let `M` be a unitary matrix over
   `E ⊗[F] R` with `M₀₁ = M₁₀ = 0`. Then `M₀₀` is a unit with inverse `N₀₀`, where `N` is
   the inverse matrix. The `(1,1)` entry of `M adjoint(M) = 1` gives
   `M₁₁ c_R(M₀₀) = 1`, so `M₁₁ = c_R(N₀₀)`. Hence `M = leviDiagonalUnitary R c M₀₀`.
2. Coefficients (`rightCoefficient_tmul`, `rightCoefficient_tensorCoefficientMap`,
   `eq_zero_of_rightCoefficient`). Coefficients are natural in the right factor. An element
   of `E ⊗[F] A` all of whose coefficients vanish is zero. This is proved by expanding the
   element along a basis of `E` and its coordinate functionals.
3. Levi similitudes (`similitudeMatrix_leviSimilitude`, `leviSimilitude_mem`,
   `leviSimilitude_injective`, `leviSimilitude_surjective`, `leviSimilitude_naturality`).
   The matrix of `leviSimilitude c A a` is `leviDiagonalUnitary A c a`, so it is diagonal
   with multiplier one. The map is injective because `leviDiagonalUnitary` is. For
   surjectivity, a similitude with multiplier one comes from a unitary element through
   `unitaryEquivKernel`, and step 1 applies to that element. Naturality in the coefficient
   algebra follows from `tensorMatrixEquiv_changeCoefficients` and
   `leviDiagonalUnitary_naturality`.
4. Cut-out (`similitudeHom_universalMatrix`, `mem_diagonalSimilitudes_iff_leviIdeal`,
   `isCutOutBy_leviIdeal`). The classifying homomorphism `similitudeHom b x` of a
   similitude `x` sends `μ` to its multiplier. It sends each coefficient of a universal
   matrix entry to the corresponding coefficient of the matrix entry of `x`. By step 2,
   `x` is diagonal with multiplier one exactly when `similitudeHom b x` kills
   `leviIdeal b c`. This is `Corepresented.IsCutOutBy` for the corepresented similitude
   functor.
5. Isomorphism (`pointsEquiv_leviCutPointsEquiv`, `lTensor_eq_tensorCoefficientMap`,
   `leviCutPointsEquiv_naturality`, `leviIso`). The point bijections are natural in `T`,
   by `WeilGm.pointsEquiv_naturality`, `Corepresented.pointsEquiv_naturality` and step 3.
   Hence `isoOfPoints` gives `leviIso b c`.
6. Factorization (`pointsEquiv_cutHom`, `leviHom_comp_unitaryInclusion`). On every
   `T`-point, `leviHom b c ≫ SchemeModel.unitaryInclusion b (involution c)` and
   `(leviIso b c).hom ≫ Corepresented.cutHom _` give the same similitude: the Levi
   similitude of the point. The proof uses `hom_ext_points`, `pointsEquiv_leviHom`,
   `SchemeModel.unitaryInclusion_points`, `Corepresented.groupSchemeMap_points` and
   `comp_isoOfPoints_hom`.
7. Closedness (`isClosedSubgroup_leviHom`). The underlying morphism of `leviIso` is an
   isomorphism, and `Corepresented.cutHom` is a closed immersion
   (`Corepresented.isClosedImmersion_cutHom`). So the composite of `leviHom b c` with
   `unitaryInclusion` is a closed immersion. `IsClosedImmersion.of_comp_isClosedImmersion`
   then shows that `leviHom b c` is a closed immersion.
