# A diagonal integral matrix representation of a local integral model

Author: Worker 4686.

This internal module proves the Library proposition
`Langlands.GroupScheme.IntegralModel.IntegralDiagonalRepresentationStatement`
(from `IwasawaCellLinear.lean`) at every universe `u`, as
`integralDiagonalRepresentation`. With the published
`maximalCompactStatement_of_integralDiagonalRepresentation`, the remaining
input for `MaximalCompactStatement` is the published
`LeviMaximalCocharacterStatement`, which is not proved here.

It uses three helper modules of the same contribution:
`IntegralLinearEmbedding/Comodule.lean` (matrix coefficients over a principal
ideal domain), `IntegralLinearEmbedding/Diagonalization.lean` (diagonalizing a
cocharacter of `GL_n` over a principal ideal domain) and
`IntegralModel/LocalIntegralSeparation.lean` (integral sections separate the
coordinates of the model). The module sets
`backward.isDefEq.respectTransparency false`.

Throughout, `F` is a nonarchimedean local field of either characteristic,
`G` is a group scheme over `Spec F`, and `M : IntegralModel 𝒪[F] F G`.

## The model as a corepresented group

* `coordAlg M` is the original coordinate ring of `M.group`, as an object of
  `CommAlgCat 𝒪[F]`. `coordIso M` identifies its spectrum with the model
  (inverse of the published `affineSchemeOverIso`), and `coordCorep M` is the
  published `AffineLinearEmbedding.corepresentableBy M.group (coordIso M)`.
  Through it, the published `AffineLinearEmbedding.bialgebra` makes the
  coordinate ring a bialgebra over `𝒪[F]`.
* `coordCorep_homEquiv_symm_apply`: the algebra map classifying an affine
  `A`-point `x` of the model sends a coordinate `a` to its value
  `affineSchemePointEquiv 𝒪[F] M.group.X A x a`.

## Matrix representations from matrix coefficients
(namespace `AffineLinearEmbedding`)

For a group `G` over `Spec R`, an identification `j` of `G.X` with the
spectrum of `B`, and a matrix `M` over `B` with
`comul (M i j') = ∑ l, M i l ⊗ M l j'` and `counit (M i j') = δ`:

* `yonedaGrp_preimage_hom_hom`, `modelIso_hom_hom_hom`,
  `modelIso_inv_hom_hom`: the published `modelIso G j` has underlying scheme
  maps `j.hom` and `j.inv`.
* `affinePointsEquiv_comp_inv`: the corepresentation recovers an affine point
  `x` of `G` from `x ≫ j.inv`.
* `modelRep G j M hcomul hcounit` is the matrix representation
  `(modelIso G j).inv ≫ toGLHom ...` of `G`, built from the published
  `toGLHom` of the corepresented group.
* `modelRep_affineMatrix_apply`: its matrix at an affine `S`-point `x` has
  entries `(homEquiv.symm x) (M i j')`, the matrix coefficients evaluated at
  the classifying algebra map (published
  `Corepresented.groupSchemeMap_affinePoints`).

## Matrix coefficients of the model

* `exists_integral_matrixCoefficients`: if `IsConnectedReductive G`, there are
  `N` and a matrix `Mat` over `coordAlg M` satisfying the comultiplication and
  counit identities for `coordCorep M`, whose entries generate the coordinate
  ring as an `𝒪[F]`-algebra. Proof: `𝒪[F]` is a principal ideal domain, the
  coordinate ring is flat (`flat_affineCoordinateRing`), and functionals
  separate its elements: for `b ≠ 0`, evaluation at the integral section of
  `exists_integralSection_apply_ne_zero` is a functional that is nonzero at
  `b`. Then `IntegralLinearEmbedding.exists_matrix_coefficients`, applied to a
  finite set of algebra generators, gives `Mat` whose entries span a
  submodule containing the generators.

## The generic representation

For a matrix representation `ρ₁` of the model `M.group`:

* `genericRep M ρ₁ : MatrixRepresentation G (Fin N)` is
  `M.genericIso.inv ≫ (base change of ρ₁ to F) ≫ (GeneralLinear.baseChangeIso (Fin N) _).hom`.
* `modelPoint M g` is the `F`-valued model point
  `M.genericModelPointEquiv F (rationalCoeffEquiv F G g)` underlying a rational
  point `g` of `G`.
* `baseChange_map_left_fst`, `rationalPoints_map_genericRep`,
  `baseChangeIso_entry`, `affinePointsEquiv_entry`, `modelPoint_comp_left`:
  bookkeeping lemmas on the underlying scheme maps and on the matrix entries of
  points of `GL_N` and of its base change (published
  `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom`,
  `GeneralLinear.pointsEquiv_eq_affinePointsEquiv`,
  `genericModelPointEquiv_left`, `rationalCoeffEquiv_left`). They are separate
  lemmas because one combined proof did not elaborate in reasonable time.
* `genericRep_rationalPointsEquiv`: the matrix
  `GeneralLinear.rationalPointsEquiv N _ (rationalPoints.map (genericRep M ρ₁) g)`
  equals `ρ₁.affineMatrix _ (modelPoint M g)`, the matrix of the model
  representation at the underlying `F`-valued model point. The proof compares
  entries.
* `genericCocharacter_comp_genericRep`: for a model cocharacter `χ`,
  `M.genericCocharacter χ ≫ genericRep M ρ₁` is the base change of `χ ≫ ρ₁`
  followed by `baseChangeIso`.

## Conjugation and integrality

* `affineMatrix_comp_innerIso`: composing a matrix representation with the
  inner automorphism of the point `rationalMatrixPoint B` (for `B : GL (Fin N) R`)
  conjugates its matrices by the image of `B`.
* `conj_mem_range_map_iff`: for a ring map `f : R →+* K`, `B : GL n R` and
  `A : GL n K`, the conjugate `f(B) A f(B)⁻¹` comes from `GL n R` if and only
  if `A` does.
* `modelRep_entry`: the entries of the model representation at an `F`-valued
  model point `x` are the values of the matrix coefficients at `x`.
* `modelRep_affineMatrix_changeRing`: at an `F`-point coming from an
  `𝒪[F]`-point, this matrix comes from `GL_N(𝒪[F])` (published
  `MatrixRepresentation.affineMatrix_naturality`).
* `mem_integralPoints_iff_modelRep`: if the matrix coefficients generate the
  coordinate ring, then `g ∈ M.integralPoints` if and only if the matrix of
  the model representation at `modelPoint M g` comes from `GL_N(𝒪[F])`. Forward:
  an integral point is the image of an integral section
  (`genericModelPointEquiv_integralPointMap`). Backward: the coordinates with
  value in `𝒪[F]` form a subalgebra containing all matrix coefficients, hence
  everything, and the published `mem_integralPoints_iff_genericCoordinates`
  applies.

## Main result

`integralDiagonalRepresentation : IntegralDiagonalRepresentationStatement.{u}`.
Given `F`, `G` with `IsConnectedReductive G`, `M`, the special-fibre hypothesis
(unused) and a model cocharacter `χ`:

1. `exists_integral_matrixCoefficients` gives `Mat` with generating entries,
   hence the model representation `ρ₀ = modelRep M.group (coordIso M) Mat ...`.
2. `exists_innerIso_comp_eq_diagonalCocharacter_of_isPrincipalIdealRing`
   applied to `χ ≫ ρ₀` over `𝒪[F]` gives `B : GL (Fin N) 𝒪[F]` and weights
   `e` with `χ ≫ ρ₀ ≫ (conjugation by B) = diagonalCocharacter e`.
3. The representation is `ρ = genericRep M (ρ₀ ≫ conjugation by B)`.
   Condition 1 of the statement follows from
   `genericCocharacter_comp_genericRep` and the published
   `GeneralLinear.baseChangeCocharacter_diagonalCocharacter`. Condition 2
   follows from `genericRep_rationalPointsEquiv`,
   `affineMatrix_comp_innerIso`, `mem_integralPoints_iff_modelRep` and
   `conj_mem_range_map_iff`.

## Provenance

The module is derived internally and follows the intended proof recorded in
`IwasawaCellLinear.md`. The existence of a linear representation of the model
whose matrix coefficients generate its coordinate ring is F. Bruhat and
J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
1.4.5 (printed p.25 / PDF p.22), registered as
`bruhat-tits-1984-reductive-local-groups-ii`; they deduce it from a
proposition of Serre on comodules over a Dedekind ring. Here only the matrix
coefficients and the integrality criterion are proved; no closed immersion
into `GL_N` is constructed or needed. The diagonalization over `𝒪[F]` and the
base change to `F` are internal. The Lean statements are not quoted from the
source.
