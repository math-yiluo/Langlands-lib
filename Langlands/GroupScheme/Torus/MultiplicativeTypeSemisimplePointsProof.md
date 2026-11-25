# Multiplicative type via semisimple geometric points: proof

`Langlands.GroupScheme.multiplicativeTypeSemisimplePoints` proves
`Langlands.GroupScheme.MultiplicativeTypeSemisimplePointsStatement.{u}`
(Milne, *Algebraic Groups* (2017), Corollary 12.21; see
[`MultiplicativeTypeSemisimplePointsStatement`](MultiplicativeTypeSemisimplePointsStatement.md)).
The data are a field `k : Type u`, a group scheme `G` over `Spec k` with
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `IsCommMonObj G.X`. Write
`kᵃ = AlgebraicClosure k`. The claim is that `IsMultiplicativeType G` holds
if and only if, for every `ρ : MatrixRepresentation G (Fin n)` and every
`kᵃ`-point `x` of `G`, `Matrix.toLin' (ρ.affineMatrix kᵃ x)` is semisimple.

## Route

The proof does not follow Milne's route through a faithful representation and
the diagonal subgroup `D_n`. It works with the coordinate Hopf algebra
`H = AffineCoordinates.hopfAlgebra G` and its scalar extension `kᵃ ⊗[k] H`.
The key equivalence is: `G` is of multiplicative type iff `kᵃ ⊗[k] H` is
spanned by its group-like elements. A point `x` corresponds to an algebra map
`f : H → kᵃ`, and `ρ(x)` is `M.map f`, where `M` is a matrix of matrix
coefficients of `H` (entries `M i j` with
`comul (M i j) = ∑ l, M i l ⊗ M l j` and `counit (M i j) = δ i j`). The linear
algebra relating group-like spanning and semisimplicity of the matrices
`M.map f` is in the helper module
[`SemisimplePointsCoefficients`](SemisimplePointsCoefficients.md). The
declarations below are in the namespace
`Langlands.GroupScheme.SemisimplePoints`, except the final theorem. Throughout,
`IsAffine G.X.left` is a section variable; the final theorem obtains it from
`IsAffineHom G.X.hom` by Mathlib's `isAffine_of_isAffineHom`.

## Points and matrix coefficients (`section Coordinates`)

Let `e = AffineCoordinates.corepresentation G` be the corepresentation of the
point functor of `G` by its coordinate algebra, and
`iG = AffineCoordinates.groupSchemeIso G` the isomorphism from the
corepresented group scheme `Corepresented.groupScheme (functor G) e` to `G`.

- `affineMatrix_eq_map_universalMatrix`: for `ρ : MatrixRepresentation G n`,
  a test algebra `S` and an `S`-point `x`, the matrix `ρ.affineMatrix S x` is
  the library's `Unipotent.universalMatrix e (ρ.restrict iG.hom)` with the
  algebra map classifying `x ≫ iG.inv` applied to its entries. The classifying
  map is the preimage under the fully faithful relative spectrum
  `algSpec`. The proof rewrites with `Unipotent.affineMatrix_classifiedPoint`
  and `MatrixRepresentation.affineMatrix_restrict`, uses
  `Functor.FullyFaithful.map_preimage`, and cancels `iG.inv ≫ iG.hom`.
- `comul_universalMatrix_hopf` and `counit_universalMatrix_hopf`: the
  universal matrix of any representation of the corepresented model is a
  matrix of matrix coefficients for the comultiplication and counit of the
  Hopf algebra `H`. These combine the library's
  `Unipotent.comul_universalMatrix` / `Unipotent.counit_universalMatrix`
  (stated for the coalgebra structure `AffineLinearEmbedding.comul e`,
  `AffineLinearEmbedding.counit e`) with
  `AffineCoordinates.corepresentation_comul` /
  `AffineCoordinates.corepresentation_counit`, which identify these maps with
  the Hopf structure maps of `H`.

## (⇒) (`section Forward`)

- `span_algebraicClosure_of_isMultiplicativeType`: if `G` is of
  multiplicative type then `kᵃ ⊗[k] H` is spanned by group-like elements.
  The library theorem
  `MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic`
  shows that the base change `G_{kᵃ}` is of multiplicative type;
  `MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed` (`kᵃ` is
  separably closed) gives an isomorphism `d : G_{kᵃ} ≅ D(Λ)`. Composing
  `SplittingAssembly.scalarExtensionCoordinatesIso G` (Hopf spectrum of
  `kᵃ ⊗[k] H` ≅ `G_{kᵃ}`), `d`, and the inverse of
  `Diagonalizable.hopfSpecIso` gives an isomorphism of Hopf spectra of
  `kᵃ ⊗[k] H` and the group algebra `kᵃ[Λ]`; `SplittingAssembly.span_of_hopfSpecIso`
  transports Mathlib's `AddMonoidAlgebra.span_isGroupLikeElem`.
- `isSemisimple_of_isMultiplicativeType`: rewrite `ρ.affineMatrix kᵃ x` by
  `affineMatrix_eq_map_universalMatrix` and apply the helper
  `isSemisimple_of_span_baseChange` to the universal matrix, using the
  previous two bullets. This direction uses neither smoothness nor
  commutativity.

## (⇐) (`section Backward` and `section Assembly`)

- `closurePoint G f`: for `f : H →ₐ[k] kᵃ`, the `kᵃ`-point of `G` obtained
  as the spectrum of `f` (`Unipotent.classifiedPoint e f`) followed by
  `iG.hom`.
- `coefficientRepresentation G M hcomul hcounit`: for a matrix of matrix
  coefficients `M : Matrix (Fin N) (Fin N) H`, the representation
  `iG.inv ≫ AffineLinearEmbedding.toGLHom e M _ _` of `G`. The coefficient
  identities for `AffineLinearEmbedding.comul e` and `counit e` required by
  `toGLHom` are obtained from those of `H` by
  `AffineCoordinates.corepresentation_comul` / `_counit`.
- `affineMatrix_coefficientRepresentation`: the matrix of
  `coefficientRepresentation G M _ _` at `closurePoint G f` is `M.map f`.
  After cancelling `iG.hom ≫ iG.inv`, the point is the spectrum of `f` on the
  corepresented model; `Corepresented.groupSchemeMap_affinePoints` and
  `Corepresented.affinePointsEquiv_map` reduce the matrix to
  `AffineLinearEmbedding.matrixHom`, whose entries are `f (M i j)`.
- `commute_and_isSemisimple`: assume the semisimplicity hypothesis of the
  statement and `IsCommMonObj G.X`. For a matrix of matrix coefficients `M`
  of `H`, the matrices `M.map f` (`f : H →ₐ[k] kᵃ`) are semisimple, by the
  hypothesis applied to `coefficientRepresentation` at `closurePoint G f`.
  They commute pairwise: `ρ.affineMatrix kᵃ` is a monoid homomorphism from
  the group of `kᵃ`-points (with the group law of `G.X`) to `GL_N(kᵃ)`, and
  this group is commutative by Mathlib's scoped instance `Hom.commMonoid`
  for `IsCommMonObj`.
- `isMultiplicativeType_of_isSemisimple` (assumes `[Smooth G.X.hom]`):
  smoothness supplies the instances that `kᵃ ⊗[k] H` is reduced
  (`AffineCoordinates.hopfAlgebraBaseChangeReduced`, `kᵃ` being a domain) and
  of finite type over `kᵃ` (`AffineCoordinates.hopfAlgebraBaseChange_finiteType`).
  The helper `span_baseChange_of_isSemisimple` then shows that `kᵃ ⊗[k] H`
  is spanned by group-like elements. Its hypothesis that every `b : H` lies
  in the span of the entries of a matrix of matrix coefficients is the
  library's `AffineLinearEmbedding.exists_matrix_coefficients` applied to
  `{b}`; its second hypothesis is `commute_and_isSemisimple`. Let
  `Λ = Additive (GroupLike kᵃ (kᵃ ⊗[k] H))`. It is finitely generated by the
  helper `addGroupFG_groupLike`. The bialgebra equivalence
  `kᵃ ⊗[k] H ≃ kᵃ[Λ]` (`Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike`
  followed by Mathlib's `MonoidAlgebra.toAdditiveBialgEquiv`), made into an
  isomorphism of commutative Hopf algebras by `CommHopfAlgCat.isoMk` and
  mapped by the Hopf spectrum functor, composed with
  `SplittingAssembly.scalarExtensionCoordinatesIso G` and
  `Diagonalizable.hopfSpecIso`, gives
  `G_{kᵃ} ≅ D(Λ)` over `Spec kᵃ`. So `G` is of multiplicative type, with the
  field `kᵃ` as witness.

## Final theorem

`multiplicativeTypeSemisimplePoints` introduces the data, obtains
`IsAffine G.X.left`, and combines `isSemisimple_of_isMultiplicativeType` and
`isMultiplicativeType_of_isSemisimple`.

The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
