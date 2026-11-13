# The split orthogonal group scheme in matrix coordinates

This internal derived construction defines `OrthogonalMatrix.groupScheme l R` for a
finite index type `l : Type` and a commutative base ring `R`. It is the orthogonal
group `O_{2|l|}` over `Spec R` of the split (hyperbolic) quadratic form

`q(x) = ∑ a, x (inl a) * x (inr a)`

on row vectors `x` indexed by `l ⊕ l`.

## Alternating matrices and the defect

`IsAlt M` says that a square matrix has the form `U - Uᵀ`. `isAlt_iff` shows that
this holds exactly when `M + Mᵀ = 0` and every diagonal entry of `M` vanishes; the
witness is the strictly upper triangular part `strictUpper M` for the order of the
indices given by `Fintype.equivFin`. Alternating matrices are closed under sums,
negation, congruence `M ↦ g M gᵀ` (`IsAlt.conj`) and entrywise ring maps.

`formMatrix l A` is the Gram matrix `Q = [[0, 1], [0, 0]]` of `q`, so that
`q(x) = x Q xᵀ`, and `polarMatrix l A` is `J = Q + Qᵀ = [[0, 1], [1, 0]]`, the matrix
of the polar bilinear form. The defect of a matrix is `defect g = g Q gᵀ - Q`; it
satisfies `defect (g h) = g (defect h) gᵀ + defect g` (`defect_mul`), its symmetric
part is `g J gᵀ - J` (`defect_add_transpose`), and its diagonal entry at `i` is
`q` of the `i`-th row of `g` (`defect_apply_self`).

## Orthogonal matrices

`orthogonalGroup l A` is the set of `g ∈ M_{l ⊕ l}(A)` whose defect is alternating,
i.e. `g Q gᵀ ≡ Q` modulo alternating matrices. This is the standard way to say that
`g` preserves the quadratic form `q` in every characteristic: the quadratic form
`x ↦ x M xᵀ` determines `M` exactly modulo alternating matrices. By `isAlt_iff`
the condition is equivalent (`mem_orthogonalGroup_iff'`) to

- `g J gᵀ = J`, i.e. `g` preserves the polar form, and
- `∑ a, g i (inl a) * g i (inr a) = 0` for every row index `i`.

The set is a submonoid by `defect_mul`. Such a matrix is invertible with inverse
`invMatrix g = J gᵀ J` (`mul_invMatrix`, and `invMatrix_mul` by Mathlib's
`mul_eq_one_comm` for square matrices over a commutative ring), and the inverse is
again orthogonal (`invMatrix_mem`), so `orthogonalGroup l A` is a group.
`OrthogonalMatrix.map` applies a ring homomorphism entrywise, and `toGL` includes
orthogonal matrices into invertible matrices.

## The coordinate ring and the group scheme

The coordinate ring is

`R[X_(i,j) : i, j ∈ l ⊕ l] / (entries of D + Dᵀ, diagonal entries of D)`,

where `D = defect X` for the generic matrix `X = genericMatrix l R`. There are no
inverse variables. `OrthogonalMatrix.homEquiv` identifies `R`-algebra maps out of
the coordinate ring with orthogonal matrices over the target: `point` specializes the
universal matrix `universal l R`, `classify` sends a matrix to the evaluation at its
entries (it kills the ideal by `ideal_le_ker`), and polynomial and quotient
extensionality show that they are inverse. The identification commutes with algebra
maps (`point_comp`, `classify_map`).

The published `Corepresented.groupScheme` then puts the group-scheme structure on the
relative spectrum of this ring, through the functor `OrthogonalMatrix.functor l R`
of orthogonal matrices and its corepresentation `corepresentableBy l R`. The
structure morphism is affine. `pointsEquiv l R T` is the natural group equivalence,
for every relative test scheme `T`, between scheme points and orthogonal matrices over
`Γ(T, O_T)`; restriction along a morphism of test schemes applies the pullback
entrywise (`pointsEquiv_naturality`).

`OrthogonalMatrix.inclusion` is the morphism into the published general linear group
scheme of `l ⊕ l`, induced by `toGL`. `baseChangeModelIso` identifies the base change
of the model along any morphism `Spec R' ⟶ Spec R` with the model over `R'`; on every
test scheme it preserves all matrix entries (`pointsEquiv_baseChangeModelIso_hom`).

## Provenance and scope

The provenance is elementary quadratic-form algebra (a quadratic form on a free
module is `x ↦ x M xᵀ` with `M` determined modulo alternating matrices) and the
Library's corepresented group construction; the layout follows the Library's
`SymplecticMatrix.groupScheme`. The model works over every commutative ring so that
base change and smoothness can be proved in coordinates. It is the split form used to
study the orthogonal groups `(FirstKindInvolution.scalar K).isometryGroup q` of
nondegenerate quadratic forms of even rank. This module proves no smoothness,
connectedness or reductivity statement and compares the model with no other group
scheme of the Library.
