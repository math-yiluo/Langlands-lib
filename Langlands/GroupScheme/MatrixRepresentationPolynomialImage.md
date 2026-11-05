# Polynomial equations for actual affine-point matrix images

Authors: Worker 1571 and Worker 1359. Worker 1359 identified the existing
`Dynamic.embeddingIdeal` comparison as the bridge to the polar construction;
Worker 1571 implemented the coefficient and range comparisons here.

Let `k : Type u` be a field, `G` an actual group scheme over `Spec k`, and
`ρ : G ⟶ GL_n` an actual homomorphism whose underlying scheme morphism is a
closed immersion. The finite index type is `n : Type`; it can be empty. For
every commutative `k`-algebra `S : Type u`, the range in this module is that of
`ρ.affineMatrix (CommAlgCat.of k S)` on the existing actual scheme-point
carrier. No replacement of the carrier or its topology is made.

`affineImageEquations S` is the set of polynomials in matrix and inverse-entry
coordinates obtained by extending the coefficients of `Dynamic.embeddingIdeal ρ`
from `k` to `S`. This ideal and its zero-locus factorization theorem already
exist in `Dynamic.OppositeCellEmbedding`.

`mem_affineMatrix_range_iff_zeroLocus` uses that factorization theorem. The
existing `pointMatrix_eq_affineMatrix` identifies the matrix read over the
global sections of `Spec S` with the actual affine coefficient matrix after
applying the canonical algebra equivalence `S ≃ₐ[k] Γ(Spec S, ⊤)`. Entrywise
injectivity of this equivalence makes equality of the transported matrices
equivalent to equality of the original matrices. Thus the zero-locus witnesses
are exactly the preimages under the actual affine matrix homomorphism.

`mem_affineMatrix_range_iff_equations` rewrites evaluation over `k` as evaluation
of the coefficient-extended polynomial over `S`. Its two implications use the
literal image-set definition of `affineImageEquations`. When `S` is an `RCLike`
field, `affineMatrix_range_isPolynomiallyDefined` packages this equivalence as
`AlgebraicMatrixPowers.IsPolynomiallyDefined`.

This is an internal comparison of published coordinate constructions, requiring
no new literature assertion. It discharges polynomial definability for any
supplied scheme-theoretic closed representation on its actual affine points.
It does not supply an adjoint-compatible representation of a reductive group,
a diagonal cocharacter adapted to an arbitrary actual parabolic, or the full
archimedean Iwasawa theorem.
