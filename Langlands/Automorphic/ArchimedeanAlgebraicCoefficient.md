# Algebraic coefficients on the actual archimedean group and Lie algebra

Author: Worker 2.

This internal construction attaches an actual finite-product general linear
scheme representation to the completion-based archimedean group and its
complexified Lie algebra on the same full coefficient space. It derives the Lie
action and conjugation covariance from the published algebraic differential.
It then discharges the coefficient covariance hypothesis for the actual
automorphic tensor construction. The main point representation is
`Langlands.Automorphic.ArchimedeanAlgebraicCoefficient.representation`.

## Embeddings and independent universes

Let `F : Type uF` be a field, `n : ℕ`, and `I : Type` an index in universe
zero. Let

```text
e : I → Langlands.Global.ArchimedeanGL.EmbeddingIndex F.
```

The published `EmbeddingIndex F` has one label at each real infinite place
and two labels, indexed by `Bool`, at each complex infinite place.
`embeddingComponent F` is respectively the real coordinate included in
`ℂ`, the complex coordinate, or its complex conjugate. The definitions
below use these actual real algebra maps. In particular, selecting the
conjugate label applies complex conjugation to the matrix entries.
There is no assumption that `e` is injective, surjective or nonempty.

When `[NumberField F]`, `fullEmbeddingEnumeration F` is an equivalence
from `Fin (Fintype.card (EmbeddingIndex F))` to the complete embedding
index. It is the inverse of Mathlib's finite enumeration. Taking its
underlying function for `e` includes every real label and both complex
orientations. The finite source lies in universe zero even when `F` is in a
higher universe. Thus the complex coefficient field is never forced into
the field's universe. The elementary coordinate constructions themselves
do not require the number field hypothesis.

## Actual group and Lie coordinates

The following declarations are in `Langlands.Global.ArchimedeanGL`.
`embeddingMatrixHom F n e` is the real algebra homomorphism

```text
ArchimedeanMatrix F n →ₐ[ℝ] (I → Matrix (Fin n) (Fin n) ℂ)
```

whose component is entrywise application of `embeddingComponent F (e i)`.
`embeddingMatrixHom_apply` states this entry formula.
`embeddingGL F n e` first applies the published actual group coordinate
equivalence `archimedeanGLCoordinates F n`, then maps the resulting units
along the same entrywise algebra maps. Its domain is the full
`InfiniteAdelicGL F n`; its codomain is `I → GL (Fin n) ℂ`.
`embeddingGL_val` and `embeddingGL_entry` identify its matrix and entry
coordinates.

`embeddingRealLieHom` applies that real algebra homomorphism to the
published actual real matrix Lie algebra. Its bracket is the matrix
commutator. Bracket preservation follows by mapping subtraction and both
matrix products. `embeddingComplexLieLinear` is its complex-linear
scalar extension from `ℂ ⊗[ℝ] RealLieAlgebra F n`, constructed with
`TensorProduct.AlgebraTensorModule.lift`.
`embeddingComplexLieHom` bundles the same linear map as a complex Lie
homomorphism. The proof uses tensor induction in both variables. On pure
tensors the published scalar-extension bracket is
`⁅z ⊗ X, w ⊗ Y⁆ = (z*w) ⊗ ⁅X,Y⁆`; linearity, the real Lie
homomorphism law and complex bilinearity give the required bracket law.
The additive cases use additivity of the bracket and linear map.

`embeddingComplexLieLinear_tmul` and `embeddingComplexLieHom_tmul`
state `φ(z ⊗ X) = z • φℝ(X)`.
`embeddingComplexLieHom_tmul_entry` gives the individual entry
`z * embeddingComponent F (e i) (X a b)`, with `X` read through
`realLieAlgebraToMatrix F n`.

Both embedding Lie maps intertwine the actual adjoint action with
componentwise conjugation by `embeddingGL`. The real result
`embeddingRealLieHom_conjugation` follows by mapping the published
formula `Ad(g)X = g X g⁻¹`. The complex result
`embeddingComplexLieHom_conjugation` extends it by tensor induction
and complex linearity. These laws hold for every element of the full
completion-based group.

## Full algebraic coefficient space and derived action

The remaining declarations are in
`Langlands.Automorphic.ArchimedeanAlgebraicCoefficient`.
Assume `[Finite I]`, and let `m : Type` have `Fintype` and
`DecidableEq` instances. The supplied datum is an actual scheme morphism

```text
ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme
    (fun _ : I => Fin n) (CommRingCat.of ℂ)) m.
```

Its source is the categorical finite product of the rank `n` general
linear group schemes over `ℂ`. No point representation, differential
or covariance witness is independently supplied.

`Space e ρ` is the full coordinate space `m → ℂ`, tagged by the
embedding map and scheme representation. The additive, complex module,
free and finite module instances are inherited from that coordinate space.
`coordinates e ρ` is the identity complex linear equivalence to
`m → ℂ`. Empty indices, rank zero and the zero coefficient space
are allowed; no irreducibility, nonzeroness, weight, norm or topology
is assumed.

Write `Dρ` for the published `ρ.productDifferential ℂ`.
`lieAction e ρ` composes the constructed product Lie differential action
with `embeddingComplexLieHom F n e`. The `LieRingModule` instance
pulls back the endomorphism action along this Lie homomorphism; the
`LieModule` instance follows from scalar linearity in both arguments.
`coordinates_lie` states

```text
coordinates(⁅X,v⁆) = Dρ(φ(X)) *ᵥ coordinates(v).
```

`coordinates_lie_tmul` specializes this to
`z • (Dρ(φℝ(X)) *ᵥ coordinates(v))` at `z ⊗ X`.
The differential is the one already constructed from actual dual-number
points of `ρ`, rather than an action assumed to have the required laws.

`reducedLieAction` and `compactLieAction` restrict this same action
along the actual reduced and compact complex Lie algebra inclusions.
`reducedLieAction_compact` proves that compact restriction through
the reduced algebra is exactly the direct compact action, using the
published equality of the two inclusions.

## Point action, covariance and actual tensors

`representation e ρ` composes the published actual product-point
representation with `embeddingGL F n e`, on `Space e ρ`.
`coordinates_representation` states that every group element acts by
left matrix multiplication by the evaluated scheme representation
`ρ.productMatrixPointsHom ℂ (embeddingGL F n e g)`.

`representation_lie` proves, for every `g`, `X` and `v`,

```text
representation(g) ⁅X,v⁆ = ⁅Adℂ(g)X, representation(g)v⁆.
```

Apply the injective coordinate equivalence, the two action formulas,
and the embedding complexification's conjugation formula. The published
`productDifferential_conjugate` computes the resulting differential.
Associativity and cancellation of the evaluated inverse matrix prove
the equality on every coefficient vector. This is algebraic covariance
for the whole group, including disconnected components.

`compactRepresentation` restricts precisely that point action to the
full `standardInfiniteCompact F n`.
`compactRepresentation_apply` identifies the restriction and
`compactRepresentation_lie` specializes the proved full-group covariance.

Finally assume `[NumberField F]` and let
`S : OperatorRealization F n` be an actual automorphic realization.
`tensorCompactRepresentation_lie` proves compact covariance of the
published diagonal complex Lie action on `S.Space ⊗[ℂ] Space e ρ`.
It applies the existing tensor covariance theorem with the coefficient
representation and its covariance law just constructed here. Thus the
coefficient hypothesis of that theorem is discharged from `ρ`.
The automorphic factor retains its actual differential operators.
The general reduced, compact, finite translation and horizontal
constructions already apply to these same coefficient instances.

## Internal provenance and remaining comparisons

This is an internal composition of published constructions:
`RegularAlgebraic` supplies the actual oriented embedding maps;
the archimedean group, Lie algebra and adjoint interfaces supply the
completion coordinates, scalar extension and conjugation;
`MatrixRepresentationProductDifferentialModule` and its imports supply
the actual point representation, dual-number differential, Lie action
and differential conjugation; `TensorLieAction` supplies actual
automorphic tensors and their conditional covariance theorem.
Mathlib supplies finite enumeration, maps on units, the scalar extension
universal property, endomorphism actions and matrix identities.
All new intrinsic laws above are proved in Lean. No new identification
with external literature is asserted.

This module supplies an algebraic differential attached to the genuine
coefficient representation. It does not prove equality with analytic
differentiation of the archimedean or compact point action, continuity or
smoothness of that action, compact infinitesimal insertion on coefficient
cochains, a general coefficient relative differential or cohomology,
cohomological nonvanishing, an infinitesimal character or highest weight,
regular algebraicity, or automorphic occurrence. Those remain separate
comparison and construction obligations.
