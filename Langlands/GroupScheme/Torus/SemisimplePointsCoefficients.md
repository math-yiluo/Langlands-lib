# Matrix coefficients, group-like elements and semisimplicity

Author: Worker 906.

This helper module holds the pure algebra used by the proof of Milne,
*Algebraic Groups* (2017), Corollary 12.21, in
[`MultiplicativeTypeSemisimplePointsProof`](MultiplicativeTypeSemisimplePointsProof.md).
Everything lives in the namespace `Langlands.GroupScheme.SemisimplePoints`.
The module contains no definitions; all declarations are theorems.

The basic notion throughout is a *matrix of matrix coefficients*: a square
matrix `N` with entries in a coalgebra `C` over a field such that

```text
comul (N i j) = ∑ l, N i l ⊗ N l j      and      counit (N i j) = (1 : Matrix) i j.
```

These are the coefficients of a finite-dimensional comodule with respect to a
basis, i.e. of a representation of the corresponding affine group.

These results are internal; they are not stated in the literature in this form.
They are standard facts about comodules and diagonalizable groups: compare
Milne, *Algebraic Groups* (2017), Theorem 12.12 (representations of
diagonalizable groups are diagonalizable), Section 12.c, and the proof of
Corollary 12.21 on printed p. 239.

## Eigenvectors (`section Eigen`)

`isSemisimple_of_span_eigenvectors`: let `f` be an endomorphism of a vector
space `V` over a field `K` and `s` a finite set of scalars. If `V` is spanned
by eigenvectors whose eigenvalues lie in `s`, then `f` is semisimple. Proof:
the polynomial `∏_{μ ∈ s} (X - μ)` is separable, hence squarefree, and it
kills each spanning eigenvector, hence all of `V`; Mathlib's
`Module.End.isSemisimple_of_squarefree_aeval_eq_zero` concludes.

## Group-like spanning gives semisimple matrices (`section Coefficients`)

`isSemisimple_map_of_span_groupLike`: let `C` be a coalgebra over a field
`K` spanned by its group-like elements, `N : Matrix n n C` a matrix of matrix
coefficients and `ψ : C →ₗ[K] K` any linear functional. Then
`Matrix.toLin' (N.map ψ)` is semisimple.

Proof. The group-like elements form a basis `b` of `C`
(`Langlands.GroupLike.basisOfSpan`). Write `N i j = ∑_g c g i j • g` over a
finite set `S` of group-like elements, with scalar matrices `c g`. Applying
the counit gives `∑_g c g = 1`; applying the functional
`x ⊗ y ↦ (coord g x)(coord h y)` to the comultiplication identity gives
`c g * c h = if g = h then c g else 0`. So the `c g` are orthogonal
idempotents summing to `1`, and `N.map ψ = ∑_g ψ(g) • c g`. Every vector `w`
is `∑_g c g w`, and `c g w` is an eigenvector of `N.map ψ` with eigenvalue
`ψ(g)`; the eigenvector criterion above applies with the finite set
`{ψ(g) : g ∈ S}`.

## Reconstruction of group-like elements (`section Reconstruction`)

`mem_span_groupLike_of_isSemisimple`: let `K` be algebraically closed and `C`
a reduced commutative `K`-bialgebra of finite type. Let `N : Matrix n n C` be
a matrix of matrix coefficients such that the matrices `N.map ψ`, for
`ψ : C →ₐ[K] K`, commute pairwise and are each semisimple. Then every entry
`N i j` is a `K`-linear combination of group-like elements.

Proof. The commuting family `ψ ↦ Matrix.toLin' (N.map ψ)` has a simultaneous
decomposition of `n → K` into common generalized eigenspaces (Mathlib's
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`);
by semisimplicity these are common eigenspaces. Let `v ≠ 0` be a common
eigenvector, `N.map ψ *ᵥ v = χ(ψ) • v`, and put `T b v = ∑_l v l • N b l`. Choose
`a` with `v a ≠ 0` and set `g = (v a)⁻¹ • T a v`. For every `ψ`,
`ψ (T l v) = χ(ψ) * v l`, so `T l v - v l • g` vanishes at all `K`-points;
by the Nullstellensatz (`StabilizerImageDichotomy.isNilpotent_of_forall_algHom`)
it is nilpotent, hence zero since `C` is reduced. Thus `T l v = v l • g` for
all `l`. The counit of `g` is `1` and the comultiplication identity gives
`comul g = g ⊗ g`, so `g` is group-like and every `T b v` lies in the span of
group-like elements. Since such `v` span `n → K`, taking `v = Pi.single j 1`
gives `N i j = T i v` in the span.

## Finite generation (`section FiniteGeneration`)

`addGroupFG_groupLike`: a commutative Hopf algebra `C` of finite type over a
field `K`, spanned by its group-like elements, has a finitely generated group
of group-like elements. The library equivalence
`Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` identifies `C` with the
group algebra of `GroupLike K C`, transported to an additive group algebra by
Mathlib's `MonoidAlgebra.toAdditiveBialgEquiv`; Mathlib's
`AddMonoidAlgebra.finiteType_iff_group_fg` turns finite type of this algebra
into finite generation of the group.

## Scalar extension (`section BaseChange`)

Here `k` and `K` are fields with `Algebra k K`, `H` is a commutative Hopf
algebra over `k`, all in universe `u`, and `n` is a finite index type.

- `comul_one_tmul_matrix` and `counit_one_tmul_matrix`: if `M` is a matrix of
  matrix coefficients of `H`, then `M.map (1 ⊗ₜ ·)` is a matrix of matrix
  coefficients of the `K`-coalgebra `K ⊗[k] H`. The comultiplication case uses
  `CentralSurjectionImage.EigenGrading.comul_one_tmul`.
- `isSemisimple_of_span_baseChange`: if `K ⊗[k] H` is spanned by group-like
  elements, `M` is a matrix of matrix coefficients of `H` and `f : H →ₐ[k] K`,
  then `Matrix.toLin' (M.map f)` is semisimple. Apply
  `isSemisimple_map_of_span_groupLike` to `M.map (1 ⊗ₜ ·)` and the functional
  given by the `K`-algebra extension `CentralSurjectionImage.EigenGrading.extend f`,
  which sends `1 ⊗ₜ b` to `f b`.
- `span_baseChange_of_isSemisimple`: let `K` be algebraically closed and
  `K ⊗[k] H` reduced and of finite type over `K`. Assume (`hcoeff`) every
  `b : H` lies in the `k`-span of the entries of some matrix of matrix
  coefficients `M : Matrix (Fin N) (Fin N) H`, and (`hpts`) for every such `M`
  the matrices `M.map f`, `f : H →ₐ[k] K`, commute pairwise and are
  semisimple. Then `K ⊗[k] H` is spanned by its group-like elements. Proof: a
  `K`-algebra map `K ⊗[k] H → K` restricts to a `k`-algebra map `H → K`, so
  `mem_span_groupLike_of_isSemisimple` applies to `M.map (1 ⊗ₜ ·)` and puts
  each `1 ⊗ₜ b` in the span; pure tensors `a ⊗ₜ b = a • (1 ⊗ₜ b)` and sums
  follow by induction on tensors.
