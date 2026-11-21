# Proof of the adapted Casimir statement on the infinite adelic points

Module `Langlands.Automorphic.GroupSchemeAdaptedCasimirProof`. The theorem
`Langlands.Automorphic.GroupSchemeFunctions.adelicAdaptedCasimir` proves exactly the Library
statement `Langlands.Automorphic.GroupSchemeFunctions.AdelicAdaptedCasimirStatement.{u}`: for a
number field `F`, an affine connected reductive group scheme `G` over `F` that is smooth of relative
dimension `d`, and a maximal compact subgroup `Kinf` of `G(F ⊗ ℝ)`, the tangent Lie algebra at `1`
of the published Lie group structure is spanned by vectors `X i` such that the `X j` with `j ∈ J`
are velocities at `0` of smooth curves through `1` in `Kinf`, and
`∑ i, X i ^ 2 - 2 • ∑ j ∈ J, X j ^ 2` is central in the actual enveloping algebra.

This is Harish-Chandra's element `ω = ω_𝔭 - ω_𝔨` (*Two theorems on semi-simple Lie groups*,
Ann. of Math. 83 (1966), proof of Lemma 33). The implemented proof uses the real trace form of
place-wise self-adjoint matrix realizations instead of the Killing form, and obtains the curves in
`Kinf` from the inverse function theorem instead of the exponential map.

## Supporting modules (all new, listed in the submission)

- `Langlands.Algebra.SignedCartanCasimir` — the algebraic signed Casimir element.
- `Langlands.Geometry.Manifold.InvolutionFixedCurve` — smooth curves of fixed points of a smooth
  involution.
- `Langlands.Geometry.Manifold.MatrixCoefficientLie` — the matrix differential is a Lie map.
- `Langlands.Geometry.Manifold.AdaptedCasimirAssembly` — the statement for an abstract Lie group
  from matrix data (`exists_adapted_casimir`).
- `Langlands.Geometry.Manifold.ZeroDirectionalDerivative` — calculus of vanishing directional
  derivatives.
- `Langlands.GroupScheme.ClosedRepresentationEvaluation` — regular functions are polynomials in
  the entries of a closed representation.
- `Langlands.Global.InfinitePlaceRealizationSmooth` — smoothness into `G(F_v)` via a closed
  realization.
- `Langlands.Global.InfiniteAdelicChartFormula` — the published chart in regular coordinates and
  joint injectivity of the realization differentials.
- `Langlands.Group.MatrixCartanInvolution` — the matrix Cartan involution.

## Auxiliary declarations in this module

- `contMDiff_mul_entries`: if the entries of `f : M → Matrix n n K` are `C^∞`, so are the entries
  of `P * f x * Q` for constant `P`, `Q` (a continuous linear function of the entries).
- `star_mem_range_of_range_eq`, `isPolynomiallyDefined_range_of_range_eq`: transport of
  star-stability and of being polynomially defined along an equality of ranges.
- `contMDiff_cartan_entries`: the entries of `R (cartan … (f m))` are smooth if those of
  `R (f m)⁻¹` are (`val_map_cartan`, conjugation is the real-linear `RCLike.conjCLE`).

## Proof of `adelicAdaptedCasimir`

Fix the data of the statement and the published charts, manifold and Lie group structure
(`smoothChartedSpace`, `smoothIsManifold`, `smoothLieGroup`).

1. **Realizations.** For each infinite place `v`, the base change `G_v` is connected reductive
   (`isConnectedReductive_completionBaseChange`), so the Library theorem
   `SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement` gives a closed matrix
   representation `ρ v` whose range on `F_v`-points is stable under conjugate transpose. Let
   `R v = realizationMatrix F G v (ρ v) : G(F_v) →* GL (Fin (N v)) F_v`. It is a closed embedding
   (`isClosedEmbedding_affineMatrix` composed with the base-change homeomorphism), its range is the
   range of `(ρ v).affineMatrix`, hence star-stable and polynomially defined
   (`affineMatrix_range_isPolynomiallyDefined`) and closed.
2. **Conjugating `Kinf`.** The image of `Kinf` under `R v ∘ atPlace F G v` is compact and lies in
   the range. The Library theorem
   `Langlands.Group.PolynomialStarCompactConjugacy.exists_conj_unitary` gives `a v` in the range
   with `a v⁻¹ * h * a v` unitary for every `h` in that image.
3. **Cartan involution.** Let `θ_v = cartan (R v) … (a v)` and let `θ` act on `G(F ⊗ ℝ)` place by
   place through the completion decomposition `completions F G`. Then `θ ∘ θ = id` and `θ 1 = 1`
   (`cartan_cartan`, `cartan_one`). By `contMDiff_iff_places` and
   `contMDiff_iff_realizationMatrix`, `θ` is smooth because the entries of `R v (θ_v x)` are
   smooth functions of the entries of `R v x⁻¹` (`contMDiff_cartan_entries`, smoothness of
   inversion).
4. **Matrix representations.** Let `φ v g = (a v⁻¹ * R v (atPlace F G v g) * a v).val`, a monoid
   homomorphism `G(F ⊗ ℝ) →* Matrix`. Its entries are smooth (`contMDiff_mul_entries`), and
   `φ v (θ g) * (φ v g)ᴴ = 1` (`val_conj_cartan_mul_conjTranspose`).
5. **Joint injectivity.** If every `matrixDifferential (φ v)` kills `X`, the entries of `φ v` have
   zero derivative along `X`; since `R v (atPlace g) = a v * φ v g * a v⁻¹`, so do the entries of
   `R v ∘ atPlace` (sums and products with constants), and
   `eq_zero_of_zeroDeriv_realization` gives `X = 0`.
6. **Fixed points lie in `Kinf`.** Let `L = ⨅ v, (cartanUnitary (R v) (a v)).comap (atPlace F G v)`.
   As a set it is the preimage under `completions F G` of a product of compact sets
   (`isCompact_cartanUnitary`), hence compact; by step 2 it contains `Kinf`; by maximality of
   `Kinf` it equals `Kinf`. A fixed point of `θ` lies in `L` (`mem_cartanUnitary_of_cartan_eq`),
   hence in `Kinf`.
7. **Conclusion.** `Langlands.Geometry.Manifold.AdaptedCasimirAssembly.exists_adapted_casimir`
   applied to `φ`, `θ` and `Kinf` gives `n`, `X`, `J` with the three required properties.
