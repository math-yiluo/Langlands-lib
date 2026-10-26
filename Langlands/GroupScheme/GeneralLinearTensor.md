# Tensor product of the actual general linear group schemes

Author: Worker 543.

This module constructs the homomorphism of group schemes

```text
tensorHom n m R :
  groupScheme n R ⊗ groupScheme m R ⟶ groupScheme (n × m) R.
```

Its domain is the actual categorical binary product of the two published
general linear group schemes over `Spec R`. Here `⊗` denotes the Cartesian
monoidal product of group objects in `Over (Spec R)`. The tensor operation
represented by the resulting morphism is the Kronecker matrix action on the
product coordinate type `n × m`; matrix Kronecker product is written `⊗ₖ`.
The module constructs the scheme morphism from its proved natural point
homomorphisms, using full faithfulness of group-valued Yoneda. Neither an
arbitrary tensor morphism nor a representability assumption is supplied.

All declarations are in `Langlands.GroupScheme.GeneralLinear`.

## Parameters and universes

The coordinate types `n m : Type` each have `Fintype` and `DecidableEq`
instances, matching the published `GeneralLinear.groupScheme` interface.
They are in universe zero. The base ring is any `R : CommRingCat.{u}`;
test schemes, their global-section rings and test algebras use this arbitrary
universe `u`. There is no field, nontriviality, positive-rank, smoothness or
reductivity hypothesis. Either coordinate type may be empty.

The matrix-only construction takes any commutative ring `A : Type u`.
Its coefficient naturality permits `B : Type v` in an independent universe
and every ring homomorphism `A →+* B`.

## The matrix homomorphism

`kroneckerHom n m A` bundles Mathlib's existing
`Matrix.GeneralLinearGroup.kronecker` as a homomorphism

```text
GL n A × GL m A →* GL (n × m) A.
```

Mathlib's invertible Kronecker matrix has value `g ⊗ₖ h` and inverse
`g⁻¹ ⊗ₖ h⁻¹`; its two inverse equations are already part of that construction.
The new homomorphism's identity and multiplication fields are proved using
`Matrix.one_kronecker_one` and `Matrix.mul_kronecker_mul`, respectively, and
extensionality of matrix units. In particular

```text
kroneckerHom (g * g', h * h')
  = kroneckerHom (g, h) * kroneckerHom (g', h').
```

`kroneckerHom_apply` identifies its value with the pinned Mathlib operation.
`kroneckerHom_coe` identifies its underlying matrix, and
`kroneckerHom_entry` gives the ordered product-basis formula

```text
kroneckerHom (g,h) (i,j) (k,l) = g i k * h j l.
```

`kroneckerHom_map` proves that applying a ring homomorphism to both input
matrices gives its entrywise application to the output matrix. The proof is
extensionality followed by preservation of multiplication by the ring map.
It assumes neither injectivity nor a common ring universe.

`kroneckerHom_mulVec` proves the identity of coordinate vectors

```text
kroneckerHom (g,h) *ᵥ (fun (i,j) ↦ v i * w j)
  = fun (i,j) ↦ (g *ᵥ v) i * (h *ᵥ w) j.
```

The implemented proof specializes `Matrix.mul_kronecker_mul` to the column
matrices of `v` and `w`, indexed by `Unit`, and evaluates the resulting
equality at a column entry. This reuses the existing matrix multiplication
identity without introducing a separate finite-sum calculation. It includes
empty indices and the zero ring.

## Construction on all test schemes

For every `T : Over (Spec R)`, `tensorPoints n m R T` is a group homomorphism
from points of the actual product to points of the target. It composes:

1. The published multiplicative equivalence `productPointsEquiv`, which
   extracts the two actual projection points.
2. The product of the published `pointsEquiv` homomorphisms, giving two
   invertible matrices over `Γ(T.left, ⊤)`.
3. `kroneckerHom` over that global-section ring.
4. The inverse of the target's `pointsEquiv`.

`pointsEquiv_tensorPoints` records this construction's matrix formula.
`tensorPoints_naturality` proves, for every `a : T' ⟶ T`, that

```text
tensorPoints T' (a ≫ x) = a ≫ tensorPoints T x.
```

The proof applies injectivity of the target's point equivalence, then uses
associativity, the published point naturality, and `kroneckerHom_map`.
The coefficient map is exactly pullback `a.left.appTop.hom`.

`tensorHom` applies the published `GroupScheme.homOfPoints` to this natural
family of homomorphisms. That constructor takes the preimage under the fully
faithful group-valued Yoneda functor. Its result is therefore an actual
morphism of group objects, with the actual scheme morphism as
`(tensorHom n m R).hom.hom`. The proof of naturality and the bundled
multiplicativity are inputs already established in this file.

`comp_tensorHom` proves that composing a point with this scheme morphism
gives `tensorPoints`. `comp_tensorHom_mul` explicitly records preservation
of multiplication of points by the actual morphism, using
`MonObj.mul_comp`.

`pointsEquiv_tensorHom` proves that the global-section matrix of the image
of any product point `x` is

```text
kroneckerHom
  (pointsEquiv n R T (x ≫ fst), pointsEquiv m R T (x ≫ snd)).
```

`pointsEquiv_lift_tensorHom` specializes this formula to the universal
pairing `lift x y` of two GL points. Its proof uses the two product
factorization identities. `pointsEquiv_tensorHom_entry` gives the
entrywise product formula on any test scheme, and
`pointsEquiv_lift_tensorHom_mulVec` transfers `kroneckerHom_mulVec` to
the matrix of the actual scheme morphism. Test schemes may be nonaffine.

## Affine formulas

For any `S : CommAlgCat.{u} R`, `affinePointsEquiv_tensorHom` gives the
same formula over `S` itself:

```text
affinePointsEquiv (n × m) R S (x ≫ tensorHom.hom.hom)
  = kroneckerHom
      (affinePointsEquiv n R S (x ≫ fst),
       affinePointsEquiv m R S (x ≫ snd)).
```

The proof applies injectivity of the target GL functor's image of
`Corepresented.affineSectionsIso S`. Its inverse identifies elements of `S`
with the global sections of the affine test scheme. The published
`pointsEquiv_eq_affinePointsEquiv`, coefficient naturality of
`kroneckerHom`, and the global-section formula then prove the result.

`affinePointsEquiv_lift_tensorHom` gives the paired-point specialization,
and `affinePointsEquiv_tensorHom_entry` gives the individual coefficient
products in `S`. `affinePointsEquiv_tensorHom_naturality` proves that
precomposing with the relative spectrum of an algebra map applies that
map entrywise to the output matrix. Its proof uses associativity and the
published affine point naturality. Finally,
`affinePointsEquiv_lift_tensorHom_mulVec` proves the decomposable-vector
action for the scheme morphism over the affine test algebra itself.

## Provenance and scope

This is internal content derived from the published actual constructions
in `Langlands.GroupScheme.GeneralLinear`,
`Langlands.GroupScheme.Products` and
`Langlands.GroupScheme.Multiplicative`, together with pinned Mathlib's
matrix identities. The Mathlib source files used are
`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` and
`Mathlib/LinearAlgebra/Matrix/Kronecker.lean`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`. No additional identification
with external literature is asserted.

The full coordinate equivalence for module tensor products is already in
`Langlands.Representation.Tensor.Coordinates`. This module does not
reconstruct it or the general matrix representation API. Its result is the
actual GL product-to-GL scheme morphism and its intrinsic point and action
formulas. Tensor products of representations from a common source group
scheme, their comparison with full module tensor representations,
differentiation and automorphic coefficient attachment remain separate work.
