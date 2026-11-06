# Compact subsets of unipotent rational points lie in compact subgroups

Author: Worker 16, as a helper for task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`
(Renard VI.1.2 and VI.1.3 for represented parabolics). Module
`Langlands.GroupScheme.Rational.UnipotentCompactSubgroups`, namespace
`Langlands.GroupScheme`.

## Provenance

Internal. The final theorem is the property "every compact subset lies in a compact
subgroup" (the condition `Jacquet.Localization.IsLimitOfCompactSubgroups` of
Bernstein–Zelevinsky) for the rational points of a unipotent group over a nonarchimedean
local field. For the unipotent radical `N(F)` of a parabolic, this is the property that
makes `N(F)` unimodular and its coinvariant (Jacquet) functor exact. The argument is the standard one. A unipotent group embeds into upper unitriangular
matrices. Conjugating by `diag(1, t, t², …)` for a small scalar `t` shrinks the
above-diagonal entries, and the matrices whose rescaled entries are integral form a compact
subgroup. No source is cited for the formal statements below, which are internal helper
results.

## Unitriangular groups

Let `F` be a nonarchimedean local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), and let `Γ` be a topological group.

`exists_isCompact_subgroup_superset_of_unitriangular` takes a group homomorphism
`φ : Γ →* GL (Fin n) F` that is a closed embedding (`IsClosedEmbedding φ`) and whose
matrices are upper unitriangular: `(φ x) i i = 1` for all `x i`, and `(φ x) i j = 0` when
`j < i`. It proves that every compact `C ⊆ Γ` lies in a subgroup `K` of `Γ` with `K`
compact.

Proof, as implemented:

1. The matrix entries of `φ x` and of `(φ x)⁻¹` are continuous in `x`. The finite union `D`
   of the images of `C` under all these entry functions is compact, so the published
   `IsCompact.exists_valuative_bound` gives `b` with `v z ≤ v b` on `D`, where `v` is the
   valuation of `F`. Choose `c ≠ 0` with `v b ≤ v c` and `1 ≤ v c` (`c = 1` or `c = b`) and
   put `t = c⁻¹`, so `v t · v c = 1` and `v t ≤ 1`.
2. Let `P x` be the condition `v ((φ x) i j · t ^ (j - i)) ≤ 1` for all `i j`, with natural
   subtraction. `P 1` holds. `P` is closed under products: in the entry
   `∑ l (φ x) i l (φ y) l j`, only terms with `i ≤ l ≤ j` survive by triangularity, and for
   them `t ^ (j - i) = t ^ (l - i) · t ^ (j - l)`, so the ultrametric inequality
   `Valuation.map_sum_le` bounds the sum. Hence `K = {x | P x ∧ P x⁻¹}` is a subgroup.
3. `C ⊆ K`: entries of `φ x` and `(φ x)⁻¹` for `x ∈ C` are bounded by `v b ≤ v c`. Above
   the diagonal `v t ^ (j - i) ≤ v t`, so the rescaled entry has valuation at most
   `v c · v t = 1`. On the diagonal the entry is `1`, and below it the entry is `0`.
4. `K` is closed, as an intersection of preimages of the closed unit ball under continuous
   maps.
5. `K` is relatively compact: an entry `m` with `v (m · t ^ k) ≤ 1` and `k ≤ n` has
   `v m ≤ v c ^ n`. So `K` maps into `Kb × Kb^op` under the closed embedding
   `Units.embedProduct ∘ φ`, where `Kb` is the compact set of matrices whose entries have
   valuation at most `v c ^ n` (`IsNonarchimedeanLocalField.isCompact_closedBall`). A
   closed subset of the compact preimage is compact.

`exists_isCompact_subgroup_superset_range` transfers the property along a closed embedding
`f : Γ →* Δ` of topological groups to the subgroup `f.range` with its subspace topology:
given compact `C ⊆ f.range`, the preimage of `C` in `Γ` is compact, it lies in a compact
subgroup `K`, and `K.map f.rangeRestrict` is a compact subgroup of `f.range` containing
`C`.

## Unipotent group schemes

Let `U` be a group scheme over `Spec F` (any field `F` in the first two results).

`pointMatrix_toGLHom_apply` is a computation. Take a matrix `M` of Hopf coordinates of `U`
satisfying the matrix-coefficient comultiplication and counit identities. Precompose the
published closed linear embedding `AffineLinearEmbedding.toGLHom` built from `M` with the
inverse of `AffineCoordinates.groupSchemeIso U`. Then the `(i, j)` entry of the point matrix
of a `T`-point `x` is the evaluation `AffineCoordinates.pointAlgebraHom U T x (M i j)`. It is
proved from the published `Corepresented.groupSchemeMap_points`.

`exists_unitriangular_closedRepresentation` assumes `[IsAffine U.X.left]`,
`[LocallyOfFiniteType U.X.hom]` and `IsUnipotent U`. It proves that there are `n` and a
matrix representation `ρ : MatrixRepresentation U (Fin n)` with `IsClosedSubgroup ρ` whose
rational matrices `ρ.rationalMatrix g` are upper unitriangular. Proof: the Hopf algebra
`AffineCoordinates.hopfAlgebra U` is of finite type
(`AffineCoordinates.algebraFiniteType`). It is unipotent, by transport of `IsUnipotent`
along `AffineCoordinates.hopfSpecIso U`. So `exists_unitriangular_matrixCoefficients` (module
`Langlands.Algebra.GradedHopf.TrivialGrading`) gives a unitriangular generating matrix `M`
of matrix coefficients. Then `ρ` is `(AffineCoordinates.groupSchemeIso U).inv ≫ toGLHom M`.
It is a closed subgroup because `AffineLinearEmbedding.isClosedSubgroup_toGLHom` applies to
generating coefficients and an isomorphism followed by a closed immersion is a closed
immersion. Rational matrix entries are evaluations of the entries of `M`
(`pointMatrix_toGLHom_apply`), so they are `1` on the diagonal and `0` below it.

Now let `F` be a nonarchimedean local field.

`exists_isCompact_subgroup_superset_of_isUnipotent` assumes `[IsAffine U.X.left]`,
`[LocallyOfFiniteType U.X.hom]` and `IsUnipotent U`. With the canonical topology
`rationalPointTopology F U.X` on `rationalPoints U`, it proves that every compact set of
rational points lies in a compact subgroup. Proof: apply the unitriangular theorem to
`ρ.rationalMatrix` for the representation above. It is a closed embedding by the published
`MatrixRepresentation.isClosedEmbedding_rationalMatrix`.

`exists_isCompact_subgroup_superset_range_of_isUnipotent` takes group schemes `G` and `U`
with `[IsAffine G.X.left]` and `[LocallyOfFiniteType U.X.hom]`, a closed subgroup
`j : U ⟶ G` (`IsClosedSubgroup j`) and `IsUnipotent U`. With the canonical topology
`rationalPointTopology F G.X` on `rationalPoints G` and the subspace topology on the image
`(rationalPoints.map j).range`, it proves that every compact subset of the image lies in a
compact subgroup of the image. Proof: `U` is affine because a closed immersion is affine.
The point map of `j` is a closed embedding by the published
`isClosedEmbedding_rationalPointMap`. Combine `exists_isCompact_subgroup_superset_range`
with the previous theorem.
