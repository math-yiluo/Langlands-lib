# Dense finite left-translation weights on archimedean compact subgroups

Module `Langlands.Global.AdelicArchimedeanFiniteWeights`, namespace
`Langlands.Global.AdelicGroupPoints`.

Let `F` be a number field and `G` an affine group scheme over `F`. The module shows the
following for a compact subgroup `C` of `G(𝔸)` contained in the archimedean factor, that is,
whose elements have finite component `1`. The continuous functions `C → ℂ` whose left
translates span a finite-dimensional space are uniformly dense in `C(C, ℂ)`. This replaces the
Peter–Weyl theorem for such groups by the Stone–Weierstrass theorem applied to the matrix
coefficients of one faithful finite-dimensional representation.

## Declarations

| Declaration | Kind | Content |
| --- | --- | --- |
| `placeRingHom F v` | definition | `F_∞ → ℂ`, the `v`-component of an infinite adele followed by `InfinitePlace.Completion.extensionEmbedding v : F_v → ℂ` |
| `continuous_placeRingHom` | theorem | it is continuous (the extension embedding is an isometry) |
| `placeMatrixRingHom F N` | definition | the ring homomorphism `M_N(F_∞) → M_{N × places}(ℂ)`, `X ↦ blockDiagonal (v ↦ X.map (placeRingHom F v))` |
| `placeMatrixRingHom_apply` | theorem | the defining formula |
| `placeMatrixRingHom_injective` | theorem | it is injective |
| `infiniteMatrix_injective` | theorem | for a matrix representation `rho : G → GL_N` that is a closed immersion, `RepresentationGrowth.infiniteMatrix F G rho : G(F_∞) → GL_N(F_∞)` is injective |
| `archimedeanMatrixRepresentation F G rho C` | definition | the representation of a subgroup `C ≤ G(𝔸)` on `ℂ^(N × places)` given by `c ↦ placeMatrixRingHom F N (rho(c_∞))`, as a linear endomorphism through `Matrix.toLinAlgEquiv'` |
| `archimedeanMatrixRepresentation_apply` | theorem | it acts by `mulVec` of that complex matrix |
| `continuous_archimedeanMatrixRepresentation` | theorem | every orbit map `c ↦ τ(c) w` is continuous |
| `archimedeanMatrixRepresentation_injective` | theorem | if `rho` is a closed immersion and every `c ∈ C` has finite component `1`, the representation is injective |
| `dense_archimedean_finiteWeights` | theorem | for `G` affine over `F` and locally of finite type, and `C` compact with trivial finite components, `Langlands.CompactRepresentativeWeights.finiteWeights` is dense in `C(C, ℂ)` |

## Proofs

`placeMatrixRingHom_injective`: the diagonal block entry at `((i, v), (j, v))` of the image of
`X` is `extensionEmbedding v (X i j v)` (`Matrix.blockDiagonal_apply_eq`). Ring homomorphisms
out of the field `F_v` are injective, so the images of `X` and `Y` agree only if every entry
of `X` and `Y` agrees at every place.

`infiniteMatrix_injective`: `infiniteMatrix` is the composite of
`G.affinePointsTarget rho` on `F_∞`-points and the homeomorphism
`GeneralLinearGroupPoints.infiniteHomeomorph F N`. The first map is an embedding by
`GroupScheme.isEmbedding_affinePointsTarget`, because `rho` is a closed immersion.

`continuous_archimedeanMatrixRepresentation`: the orbit map is
`c ↦ placeMatrixRingHom F N (rho(c_∞)) *ᵥ w`. Continuity follows from
`Continuous.matrix_mulVec`, `Continuous.matrix_blockDiagonal` and `Continuous.matrix_map`, from
the continuity of `placeRingHom`, from `Units.continuous_val`, and from the continuity of
`infiniteMatrix`, of the projection `infinite F G` and of the inclusion of `C`.

`archimedeanMatrixRepresentation_injective`: equal endomorphisms have equal matrices
(`Matrix.toLinAlgEquiv'` is injective). By the two previous injectivity results the infinite
components of the two points agree. Their finite components are both `1`, so the points agree
by `pair_projections`.

`dense_archimedean_finiteWeights`: `GroupScheme.affineLinearEmbeddingStatement_viaCorepresented`
gives a matrix representation `rho : G → GL_N` that is a closed subgroup, that is, a closed
immersion. The faithful continuous representation `archimedeanMatrixRepresentation F G rho C`
then satisfies the hypotheses of `Langlands.CompactRepresentativeWeights.dense_finiteWeights`.
That theorem proves the density from Mathlib's complex Stone–Weierstrass theorem, because the
finite-orbit functions form a star subalgebra that separates points.

## Provenance

Internal. A compact subgroup of `G(F_∞) ⊂ GL_N(F_∞)` embeds in a product of the groups `GL_N(ℂ)`,
one for each archimedean place. The matrix coefficients of this embedding, and their
conjugates, generate an algebra of functions with finite left-translation orbit, and this
algebra separates points. The density statement is the consequence of the Peter–Weyl theorem
(G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press 2015,
`folland-2015-abstract-harmonic-analysis-second`, Theorem 5.12) that is needed for compact
linear groups. The proof here uses only Stone–Weierstrass, through the Library's
`Langlands.CompactRepresentativeWeights.dense_finiteWeights`.
