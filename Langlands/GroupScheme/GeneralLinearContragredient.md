# Actual general linear contragredient automorphism

Author: Worker 2.

This module constructs the inverse-transpose automorphism of the actual
general linear group scheme over `Spec R`. It proves its formula on all
test schemes, its formula on affine points, its involutivity, and the
matrix evaluation identity needed for dual coordinate representations.
All new declarations lie in `Langlands.GroupScheme.GeneralLinear`.

## Matrix automorphism

Let `n : Type` have `Fintype n` and `DecidableEq n`, and let `A : Type u`
be any commutative ring. Empty `n` and the zero ring are allowed. The map
`matrixContragredient n A` is a multiplicative equivalence on `GL n A`.
Its value and inverse matrix at `g` are respectively

```text
value = transpose(g.inverse)
inverse = transpose(g.value).
```

Here `g.inverse` is the inverse supplied by the matrix unit. There is no
choice of an inverse or hypothesis about a separately supplied determinant.
Transposing the two original unit equations verifies the new unit equations.
Double transposition proves both inverse-function identities. Inversion and
transposition each reverse multiplication, which proves that their composite
preserves multiplication.

`matrixContragredient_coe` identifies the underlying matrix with the
transpose of the inverse. `matrixContragredient_symm` identifies the inverse
equivalence with the same map, and `matrixContragredient_involutive` records
the double-application identity.

The Library already has `Langlands.GeneralLinear.inverseTranspose d A`
for matrices indexed by `Fin d`, in `Langlands.Group.GL.Maps`.
The new construction uses the same unit formula for an arbitrary finite
index type. `matrixContragredient_fin` proves by reflexivity that
specializing the new equivalence to `Fin d` gives that published equivalence.
This preserves the existing matrix convention and avoids introducing a
different inverse-transpose operation at finite rank.

For any ring homomorphism `f : A →+* B`, with `B : Type v` in an independent
universe, `matrixContragredient_map` proves

```text
contragredient(GL(f)(g)) = GL(f)(contragredient(g)).
```

The proof is extensionality of matrix units followed by the defining
entrywise formula. Thus no field or injectivity assumption on `f` is needed.

For two coordinate column vectors `w,v : n → A`,
`matrixContragredient_pairing` proves

```text
((g.inverse)^transpose * w) dot (g * v) = w dot v.
```

The pairing is the bilinear coordinate evaluation `∑ i, w i * v i`.
It uses no complex conjugation or Hermitian form. The implemented proof
moves the transposed factor across the dot product, combines matrix-vector
multiplications, and applies the inverse matrix identity.

## Scheme automorphism

Now let `R : CommRingCat.{u}` and use the actual
`GeneralLinear.groupScheme n R` over `Spec R`.
For every `T : Over (Spec R)`, `contragredientPoints n R T` transports
`matrixContragredient n Γ(T.left, ⊤)` through the published multiplicative
equivalence `pointsEquiv n R T`.

`pointsEquiv_contragredientPoints` gives its matrix formula.
`contragredientPoints_naturality` says that for `a : T' ⟶ T`,
precomposition with `a` commutes with this operation on points.
The proof applies injectivity of `pointsEquiv`, then its naturality and
`matrixContragredient_map`. `contragredientPoints_involutive` similarly
reduces to matrix involutivity.

`contragredientIso n R` is the actual isomorphism of group schemes
constructed by the published `Langlands.GroupScheme.isoOfPoints` from this
natural family of multiplicative equivalences. That construction uses the
full faithfulness of the group-valued Yoneda functor. The result is an
actual scheme morphism preserving group multiplication, with an inverse;
representability or existence of this morphism is not an extra premise.

`comp_contragredientIso_hom` states that postcomposing a point with this
scheme morphism applies `contragredientPoints`.
`pointsEquiv_contragredientIso` therefore states that its global-section
matrix is inverse transpose.
`contragredientIso_hom_comp` proves that composing its forward morphism
with itself is the identity morphism. The proof uses the published
`hom_ext_points` and pointwise involutivity.

For `S : CommAlgCat.{u} R`,
`affinePointsEquiv_contragredientIso` gives the same formula with matrix
entries in `S` itself. The proof transports both sides through
`Corepresented.affineSectionsIso S`. The functor sends that isomorphism to
an isomorphism, so its induced function on matrices is injective. The
published global-section/affine-point comparison and coefficient naturality
then reduce the goal to `pointsEquiv_contragredientIso`.

## Provenance and scope

This is internal content. The matrix formula generalizes the already
published `Langlands.GeneralLinear.inverseTranspose`, and the explicit
finite-rank equality checks that relationship. The remaining construction
combines the published `GeneralLinear.pointsEquiv`,
`GeneralLinear.affinePointsEquiv`, their comparison and naturality, and
`GroupScheme.isoOfPoints`. The evaluation calculation uses Mathlib's
dot-product and matrix multiplication identities. No new external source
identification is asserted.

The base is affine, the coordinate type is finite, and the scheme and test
algebras use the same arbitrary universe `u`. The purely matrix coefficient
naturality lemma allows independent ring universes. No topology, positive
rank, smoothness, field or reductivity hypothesis is required.

This unit constructs the target automorphism needed to postcompose an
algebraic representation into its dual coordinate representation. That
postcomposition adapter, comparison with the full module dual, tensor
products, differentiation, and automorphic coefficient attachment are not
constructed here. In particular the pairing identity is a matrix identity,
not an assertion about a separately supplied automorphic space.
