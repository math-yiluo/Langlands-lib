# Tensor coefficients of actual group-scheme representations

Author: Worker 2.

This module constructs the tensor product of two actual finite-coordinate
representations of a common group scheme. It evaluates that scheme morphism
on test schemes, proves its Kronecker matrix formulas, and gives a bundled
equivalence between its evaluated representation and the full algebraic module
tensor product. All declarations are in
`Langlands.GroupScheme.MatrixRepresentation`.

## Parameters and actual scheme morphism

The base is any `R : CommRingCat.{u}`. The source `G` and, for restriction,
`H` are group schemes over `Spec R`. The coordinate types `n m : Type`
are in universe zero, with `Fintype` and `DecidableEq` instances. Test
schemes and test algebras use universe `u`, as in the imported actual
general linear group scheme. There is no field, nontriviality, positive
rank, smoothness, reductivity or affineness hypothesis on `G`. Empty
coordinate types and the zero base ring are allowed.

For the two morphisms

```text
ρ : MatrixRepresentation G n
σ : MatrixRepresentation G m
```

the definition `tensor ρ σ` is the composite

```text
G --lift ρ σ--> GeneralLinear.groupScheme n R ⊗ GeneralLinear.groupScheme m R
  --GeneralLinear.tensorHom n m R--> GeneralLinear.groupScheme (n × m) R.
```

Here the middle `⊗` is the Cartesian monoidal product of group objects,
and `lift` is its categorical pairing. The target is indexed by the
ordered product `n × m`. The two inputs are actual group-scheme
morphisms, and both morphisms in the composite are already constructed
in the imported Library. This definition therefore supplies an actual
group-scheme morphism, including its multiplicative structure.

`tensor_hom_hom` records definitionally that the underlying scheme
morphism is the pairing of the two underlying scheme morphisms followed
by the underlying tensor morphism. `tensor_restrict` proves, for every
group-scheme morphism `f : H ⟶ G`,

```text
(ρ.restrict f).tensor (σ.restrict f) = (ρ.tensor σ).restrict f.
```

Its proof uses associativity and the categorical `comp_lift` law; it
does not require surjectivity or injectivity of `f`.

## Matrices and coordinate actions

For any `T : Over (Spec R)` and point `x : T ⟶ G.X`,
`tensor_pointMatrix` proves

```text
(ρ.tensor σ).pointMatrix T x
  = GeneralLinear.kroneckerHom n m Γ(T.left, ⊤)
      (ρ.pointMatrix T x, σ.pointMatrix T x).
```

The proof uses `tensor_hom_hom`, naturality of categorical pairing under
precomposition, and the published `pointsEquiv_lift_tensorHom`. This
applies to nonaffine test schemes as well. The entry formula
`tensor_pointMatrix_entry` says that entry `((i,j),(k,l))` is
`ρ.pointMatrix T x i k * σ.pointMatrix T x j l`.

For `S : CommAlgCat.{u} R` and
`x : (algSpec R).obj (op S) ⟶ G.X`, `tensor_affineMatrix` proves the
same Kronecker formula over `S` itself, using the published affine
paired-point formula. `tensor_affineMatrix_entry` gives its corresponding
individual entry product. These formulas use the existing identification
of affine-scheme global sections with the test algebra.

`tensor_affineMatrix_naturality` proves that for every algebra morphism
`f : S ⟶ S'`, precomposing `x` with `(algSpec R).map f.op` applies
`f.hom.toRingHom` entrywise to the displayed Kronecker matrix. Its proof
uses the general affine coefficient naturality of the actual composite
representation. Neither the algebra map nor the point is restricted.

`tensor_affineAction` gives the action on every coordinate vector
`v : n × m → S`:

```text
(ρ.tensor σ).affineAction S x v
  = (ρ.affineMatrix S x ⊗ₖ σ.affineMatrix S x) *ᵥ v.
```

In this formula the invertible matrices are coerced to ordinary matrices,
`⊗ₖ` is the matrix Kronecker product, and `*ᵥ` is multiplication on
column vectors. The proof unfolds the established matrix action and
uses the underlying matrix of `GeneralLinear.kroneckerHom`.
`tensor_affineAction_decomposable` specializes it to

```text
(ρ.tensor σ).affineAction S x (fun (i,j) ↦ v i * w j)
  = fun (i,j) ↦ (ρ.affineAction S x v) i * (σ.affineAction S x w) j.
```

Its proof invokes the already proved `kroneckerHom_mulVec`.

## Comparison with the full module tensor representation

The imported `affineRepresentation` forgets invertibility in the affine
linear action to give Mathlib's representation of the group of `S`-points
on `n → S`. The helper `affineRepresentation_toMatrix` proves that its
matrix in the standard basis is precisely `ρ.affineMatrix S x`. It uses
the inverse law between `Matrix.toLin'` and `LinearMap.toMatrix'`.

`tensor_affineRepresentation` proves equality of representations

```text
(ρ.tensor σ).affineRepresentation S
  = CoordinateTensor.representation
      (ρ.affineRepresentation S) (σ.affineRepresentation S).
```

The proof uses extensionality of the representation homomorphisms and
their linear maps, the two Kronecker action formulas, and
`affineRepresentation_toMatrix`. The right side is the published
transport of Mathlib's full module tensor representation through
`CoordinateTensor.coordinates S n m`.

`affineTensorEquiv ρ σ S` is a bundled representation equivalence

```text
((ρ.affineRepresentation S).tprod (σ.affineRepresentation S)).Equiv
  ((ρ.tensor σ).affineRepresentation S).
```

Its underlying linear equivalence is exactly the existing
`CoordinateTensor.coordinates S n m`, derived from the tensor product
of the two standard bases. Its intertwining law follows by rewriting
`tensor_affineRepresentation` and reusing `CoordinateTensor.equiv`.
No new basis or substitute tensor carrier is introduced.

`affineTensorEquiv_tmul` gives the pure-tensor coordinate formula
`affineTensorEquiv (v ⊗ₜ w) (i,j) = v i * w j`.
`affineTensorEquiv_intertwining` explicitly records, for every tensor `t`,

```text
affineTensorEquiv (TensorProduct.map (ρ.affineRepresentation S x)
    (σ.affineRepresentation S x) t)
  = (ρ.tensor σ).affineAction S x (affineTensorEquiv t).
```

It is obtained by applying the bundled intertwining equation to `t`.
The source is the full algebraic tensor product
`(n → S) ⊗[S] (m → S)`, with no decomposability hypothesis.

## Provenance and remaining scope

This is internal content derived from the published actual
`MatrixRepresentation`, `MatrixRepresentationDual`, `GeneralLinearTensor`
and `Representation.Tensor.Coordinates` modules. It uses their actual
morphisms, point equivalences, affine actions and tensor-basis
equivalence. The additional intrinsic proofs use categorical pairing,
composition, extensionality, and Mathlib's coordinate inverse law
`LinearMap.toMatrix'_toLin'` from
`Mathlib/LinearAlgebra/Matrix/ToLin.lean`. Mathlib's bundled representation
equivalence is from `Mathlib/RepresentationTheory/Intertwining.lean`;
the pinned Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`.
No additional identification with external literature is asserted.

This unit supplies the common-source tensor scheme construction and
its full module tensor comparison. It does not construct a Lie
differential of the tensor representation, analytic or topological
tensor products, or automorphic coefficient attachment. Those remain
separate obligations in the broader definition task.
