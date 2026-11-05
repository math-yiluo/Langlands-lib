# Tensor embeddings of coordinates lying in a product of covariant spaces

Worker 1330 derives this internal support from the published regular-subspace,
covariant-product and tensor-intertwiner constructions and from the
injectivity lemma `Chevalley.coordinateProduct_injective`. It turns the
containment of a finite regular coordinate subspace in a product `X Y` of
covariant coordinate spaces into an actual injective intertwiner into a tensor
product of two finite regular representations.

Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, third enlarged edition
(1994), Appendix to Chapter 1, Section A, printed p.192, asserts that the
torus-invariant regular functions form an increasing union of copies of
`W_(mρ) ⊗ W_(mρ)`. The derivation here is the author's own and is not taken from
that page. Covariant spaces model the `W`, and the injectivity behind the word
"copies" comes from an explicit density hypothesis. The file constructs no
Borel subgroup, line bundle, Steinberg module or exhaustion; those enter only
as hypotheses.

## The covariant subspace through the Hopf coalgebra

`AffineCoordinates.leftCovariantSubspace_eq_hopf` states that the actual
covariant subspace `leftCovariantSubspace i χ` of an affine group morphism
`i : H → G` equals the general `Chevalley.leftCovariantSubspace` taken in the
coordinate Hopf algebra `hopfAlgebra G`. The restriction map is the actual
pullback `(AffineHomImageHopfAdapter.pullback i).hom.toAlgHom`. The proof
rewrites the coalgebra structure by the published
`corepresentation_coalgebra_eq`. This lets the Hopf-algebra lemma
`coordinateProduct_injective` be applied to actual covariant subspaces.

## Linear algebra

Let `k` be a field and `B` a commutative `k`-algebra.

- `exists_basis_mul_of_injective`: let `X` and `Y` be subspaces with bases `bX`
  and `bY` indexed by `Fin a` and `Fin b`. If `coordinateProduct X Y` is
  injective, there is a basis `bP` of `X * Y`, indexed by `Fin (a * b)`, with
  `bP (finProdFinEquiv l) = bX l.1 * bY l.2` for every `l`. The proof
  transports Mathlib's tensor basis `bX.tensorProduct bY` along the linear
  equivalence from `X ⊗ Y` onto the range of `coordinateProduct X Y`, which is
  `X * Y` by the published `range_coordinateProduct`, and then reindexes.
- `coactionCoordinates_mulVecLin_injective`: if `V ≤ P`, with bases `bV` and
  `bP`, the published coordinate matrix `coactionCoordinates P bP bV` is
  injective as a linear map. If it kills `x`, then every `bP`-coordinate of
  `∑ x_j bV_j` is zero. The published `basis_expand` makes the sum zero, and
  linear independence of `bV` gives `x = 0`.

## Inclusions of regular subspaces

`intertwines_coactionCoordinates` concerns a corepresented group. If `V ≤ P`
are finite regular subspaces, then `coactionCoordinates P bP bV` is an actual
intertwiner from the finite regular representation on `V` to the one on `P`.
The proof uses the published universal-point criterion
`intertwines_of_universalMatrix`, the formula
`regularRepresentation_universalMatrix`, and the coaction identity
`coactionCoordinates_mul`, applied to the basis coaction `comul_basis` of `V`.
`intertwines_affine_coactionCoordinates` restricts this to an actual affine
group through the coordinate isomorphism. This mirrors the published
`intertwines_affine_productMatrix`.

## The embedding

Let `G` have an affine structure morphism. Let `i : H → G` and `i' : H' → G`
be actual morphisms from groups with affine structure morphisms, and let
`χ` and `ψ` be coordinates of `H` and `H'`.

`exists_intertwines_tensor_of_le_mul` assumes:

- the difference comorphism of the two actual pullbacks is injective;
- `X ≤ leftCovariantSubspace i χ` and `Y ≤ leftCovariantSubspace i' ψ`, with
  bases `bX`, `bY` and stable under right translation;
- `V` is a finite right-stable subspace with basis `bV` and `V ≤ X * Y`.

It produces a matrix `C`, indexed by `Fin a × Fin b` and `Fin d`. `C` is an
actual intertwiner from the finite regular representation on `V` to the tensor
product of the finite regular representations on `X` and `Y`, and `C` is
injective.

Proof:

1. `coordinateProduct_injective`, through `leftCovariantSubspace_eq_hopf`,
   makes multiplication `X ⊗ Y → X * Y` injective.
2. `exists_basis_mul_of_injective` gives a basis `bP` of `X * Y` consisting of
   the products `bX l.1 * bY l.2`.
3. The published `affine_rightAct_mem_mul` makes `X * Y` right-stable. The
   published `intertwines_affine_productMatrix` makes the product matrix `M`
   an intertwiner from the tensor representation to the regular representation
   on `X * Y`. By step 2 and the published `extendedCoord_basis`, `M` is the
   permutation matrix of `finProdFinEquiv`. Its inverse permutation matrix `N`
   satisfies `N M = 1` and `M N = 1`. The published `Intertwines.of_mul_eq_one`
   then makes `N` an intertwiner in the other direction.
4. `intertwines_affine_coactionCoordinates` gives the inclusion intertwiner
   `J` from `V` to `X * Y`. Hence `C = N J` intertwines by `Intertwines.comp`.
5. `J` is injective by `coactionCoordinates_mulVecLin_injective`. `N` is
   injective because `M N = 1`. So `C` is injective.

## Directedness and exhaustion data

Write `X_e = leftCovariantSubspace i (χ ^ e)` and
`Y_e = leftCovariantSubspace i' (ψ ^ e)`.

- `mul_pow_le_mul_pow_succ`: if `1 ∈ X_1 * Y_1`, then
  `X_e * Y_e ≤ X_(e+1) * Y_(e+1)`. The proof multiplies by
  `1 ≤ X_1 * Y_1`, regroups the commutative product, and applies the published
  `AffineCoordinates.mul_le_leftCovariantSubspace` to each factor.
- `mul_pow_le_mul_pow`: under the same hypothesis, `X_e * Y_e ≤ X_e' * Y_e'`
  whenever `e ≤ e'`, by induction.

`exists_tensor_embedding_of_covariant_exhaustion` takes an actual
diagonalizable homomorphism `j : D(Λ) → G`, the maps `i`, `i'`, `χ`, `ψ` and
the following hypotheses:

- `hdense`: injectivity of the difference comorphism;
- `hone`: `1 ∈ X_1 * Y_1`;
- `hexh`: every coordinate that is left `j`-invariant on all test schemes lies
  in some `X_e * Y_e`;
- `hst`: for every `e` there is `e' ≥ e` such that `X_e'` and `Y_e'` have bases
  indexed by the same `Fin m`, and the finite regular representation on `X_e'`
  is rationally irreducible.

Its conclusion matches `SteinbergTensorEmbeddingStatement`: every finite
right-stable subspace `V` whose elements are left `j`-invariant on all test
schemes admits `m`, actual representations `σ` and `π` on `Fin m` with `σ`
rationally irreducible, and an injective actual intertwiner from the regular
representation on `V` to `σ ⊗ π`. The proof chooses an exponent for each basis
vector of `V` by `hexh` and takes their supremum `E`. Monotonicity gives
`V ≤ X_E * Y_E`. It then takes `e' ≥ E` from `hst` and applies
`exists_intertwines_tensor_of_le_mul` with `X = X_e'` and `Y = Y_e'`. The
published `AffineCoordinates.rightAct_mem_leftCovariantSubspace` supplies
right-stability of `Y_e'`.

## Scope

All hypotheses are explicit. No density, exhaustion, irreducibility or
dimension statement is proved here for any particular group.
