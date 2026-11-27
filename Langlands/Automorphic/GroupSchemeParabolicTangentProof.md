# The archimedean tangent grading of a rational parabolic

The module `Langlands.Automorphic.GroupSchemeParabolicTangentProof` proves
`Langlands.Automorphic.GroupSchemeFunctions.ParabolicLeviTangentGradingStatement` as the theorem
`Langlands.Automorphic.GroupSchemeFunctions.parabolicLeviTangentGrading`, for an arbitrary
universe level.

## The statement

Let `F` be a number field, `G` a connected reductive group over `F` with a parabolic subgroup
`q : Q → G`, its geometric unipotent radical `iV : V → Q` and a rational Levi subgroup
`l : M → Q`, and fix smoothness data `hG`, `hM`, `hV` for `G`, `M`, `V` (which determine the
Library atlases on the infinite adelic points). Write `𝔤 = AdelicComplexLieAlgebra F G hG`, the
complexified tangent Lie algebra at the identity of `G(F ⊗ ℝ)`. Then the radical of `𝔤` is its
centre, and there is `H ∈ 𝔤` such that the eigenvectors of `ad H` with integer eigenvalues span
`𝔤`, the complexified derivative of `l ≫ q` is injective with image the centralizer of `H`, and
the image of the complexified derivative of `iV ≫ q` is the span of the eigenvectors with
eigenvalues `1, 2, 3, …`.

## Auxiliary results in this module

- `mem_range_rationalTargetMap_iff`: membership in the image of the rational tangent map of a
  homomorphism is membership in the image of its tangent map over `F`.
- `rationalAd_eigenSet`: the eigenvectors, for rational eigenvalues `r i`, of the inner derivation
  of `h` in `RationalTangentLie F G` are the eigenvectors over `F` for the eigenvalues
  `algebraMap ℚ F (r i)`.
- `smul_mem_eigenSet`: sets of eigenvectors of `ad h` are stable under scalars of `F`.
- `rational_span_eigen_eq_top`, `mem_rational_span_positive_eigen_iff`: spans over `F` of the
  integral (respectively positive integral) eigenvectors agree with the spans over `ℚ`
  (`Langlands.Algebra.LieEigenvectorTransport.mem_span_restrictScalars_iff`).

## Proof of the theorem

The algebraic input is `Lie.exists_parabolicLieGrading` (module
`Langlands.GroupScheme.Rational.ParabolicLieGrading`), applied over `F`. It gives `H₀` in
`Lie(G)(F)` with the four properties of the statement for the tangent maps over `F`. Let `L'` be
`Lie(G)(F)` viewed over `ℚ` and `T = ad H₀` on `L'`. The analytic input is the isomorphism of
complex Lie algebras `Θ_G = complexTangentEquiv F G hG : ℂ ⊗_ℚ L' ≅ 𝔤` together with its
naturality `complexPointDifferential_complexTangentMap` (module
`Langlands.Automorphic.GroupSchemeParabolicTangentComparison`), which turns each complexified
derivative into the scalar extension of the rational tangent map, up to `Θ_M`, `Θ_V` and `Θ_G`.
Take `H = Θ_G(1 ⊗ H₀)`. On `ℂ ⊗_ℚ L'` the inner derivation of `1 ⊗ H₀` is `T.baseChange ℂ`
(`one_tmul_lie`), and `Θ_G` carries eigenvectors of `ad (1 ⊗ H₀)` to eigenvectors of `ad H` with
the same eigenvalues (`span_eigenSet_eq_map`, `lie_eq_smul_iff`).

1. *Reductivity.* `Lie(G)(F)` has central radical (`Lie.hasCentralRadical_of_isConnectedReductive`),
   hence so does `ℂ ⊗_ℚ L'` (`hasCentralRadical_baseChange_restrictScalars`), hence so does `𝔤`
   (`hasCentralRadical_of_lieEquiv`).
2. *Integral eigenvectors span.* The integral eigenvectors of `T` span `L'` over `ℚ`
   (`rational_span_eigen_eq_top`), so those of `T.baseChange ℂ` span `ℂ ⊗_ℚ L'`
   (`span_baseChange_eigen_eq_top`); apply `Θ_G`.
3. *Injectivity of the Levi differential.* The rational tangent map of `l ≫ q` is injective, its
   scalar extension is injective because `ℂ` is flat over `ℚ`
   (`Module.Flat.lTensor_preserves_injective_linearMap`), and `Θ_M`, `Θ_G` are bijective.
4. *Image of the Levi differential.* The image of the rational tangent map of `l ≫ q` is the
   kernel of `T`; by `range_baseChange_eq` and `ker_baseChange` the image of its scalar extension
   is the kernel of `T.baseChange ℂ`, that is, the centralizer of `1 ⊗ H₀`; transport by `Θ_G`.
5. *Image of the radical differential.* The image of the rational tangent map of `iV ≫ q` is the
   `ℚ`-span `W` of the positive integral eigenvectors of `T`
   (`mem_rational_span_positive_eigen_iff`); the image of its scalar extension is the image of
   `ℂ ⊗ W` (`range_baseChange_eq`), which is the span of the positive integral eigenvectors of
   `T.baseChange ℂ` (`span_baseChange_positive_eigen`); transport by `Θ_G`.

## Sources

The statement is the complexified, archimedean form of the classical grading of the Lie algebra
of a reductive group by a cocharacter defining a parabolic subgroup, with the Levi as centralizer
and the unipotent radical as the positive part (A. Borel, *Linear Algebraic Groups*, 2nd ed.,
§IV.11 and §V.20), combined with reductivity of the Lie algebra of a reductive group in
characteristic zero. The implemented proof proves the grading over `F` and transports it along
the isomorphism `ℂ ⊗_ℚ Lie(G) ≅ ℂ ⊗_ℝ Lie(G(F ⊗ ℝ))`.
