# Tensor coefficients on actual automorphic operator quotients

This internal construction is the quotient analogue of the published module
`TensorHorizontal`. It works with every number field `F : Type uF`, every
natural rank `n`, every degree `q` (including zero) and an actual
`Q : OperatorSubquotient F n`. The carrier is the original module quotient
`Q.Space = Q.upper.Space ⧸ Q.lower.toSubmodule`. Its denominator is already
invariant under the whole concrete automorphic operator algebra, and no
further invariance, covariance or finiteness hypothesis is supplied. The
coefficients are a specified complex representation `τ` of
`K = standardInfiniteCompact F n` on a complex module `V : Type v`. Its
dimension is arbitrary, and its universe is independent of the field
universe.

The declarations are in `Langlands.Automorphic.OperatorSubquotient`. Write
`Gf = FiniteAdelicGL F n`, `R(k) = Q.compactRepresentation k` and
`P(d) = Q.finiteRepresentation d`. These are the existing quotient actions,
induced from the positive right translations on the numerator. The group `K`
is the full standard infinite compact subgroup.

## Tensor actions

`tensorCompactRepresentation τ` is Mathlib's tensor product representation
`Q.compactRepresentation.tprod τ` on `Q.Space ⊗[ℂ] V`.
`tensorFiniteRepresentation V` tensors `Q.finiteRepresentation` with the
trivial representation of `Gf` on `V`. On pure tensors

`k · (f ⊗ v) = R(k) f ⊗ τ(k) v` and `d · (f ⊗ v) = P(d) f ⊗ v`.

The two `_tmul` lemmas record these formulas. No finite adelic coefficient
action is part of the input.

`tensorFiniteRepresentation_compact` proves that these two actions commute
on every tensor. The proof compares the two composite linear maps on pure
tensors (`TensorProduct.ext'`), using the published quotient commutation
`finiteRepresentation_compactRepresentation`.
`tensorFiniteCompactIntertwiner τ d` bundles each finite translation as an
intertwiner of the diagonal compact representation with itself.

## Horizontal spaces and their finite action

`tensorHorizontalSubmodule τ q` is the actual submodule
`ArchimedeanGL.horizontalEquivariantSubmodule F n
  (Q.tensorCompactRepresentation τ) q`.
Its elements are complex multilinear alternating maps from
`Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n` to `Q.Space ⊗[ℂ] V`.
Membership imposes exactly the two existing conditions:

1. the map vanishes whenever any argument comes from the complexified
   compact Lie algebra; and
2. it intertwines the reduced adjoint action of every `k : K` with
   `Q.tensorCompactRepresentation τ k`.

`tensorHorizontalFiniteRepresentation τ q` postcomposes these maps with
`tensorFiniteCompactIntertwiner τ d`, through the published
`ArchimedeanGL.horizontalMapCoefficients`. Its application lemma is

`(d · c).val x = Q.tensorFiniteRepresentation V d (c.val x)`.

The one and multiplication laws are proved by evaluating on each tuple.

`tensorInvariantsFiniteRepresentation τ` restricts finite translation to the
full-compact fixed vectors of `Q.tensorCompactRepresentation τ`. The
commutation law shows that a finite translate is still fixed by every
`k : K`.

`tensorHorizontalDegreeZeroEquiv τ` is an equivalence of finite adelic
representations from degree zero to those full-compact fixed vectors. Its
underlying linear equivalence is the published
`ArchimedeanGL.horizontalDegreeZeroEquiv`, evaluation at the unique empty
tuple (written `0` in the application lemma). Finite equivariance holds by
definition.

## The canonical projection from the numerator

`tensorCompactProjection τ` is the canonical compact projection
`Q.compactProjection` tensored with the identity intertwiner of `τ`. It is an
intertwiner from the published numerator tensor representation
`Q.upper.tensorCompactRepresentation τ` (from `TensorHorizontal`) to the
quotient one. It sends `f ⊗ v` to `Q.projection f ⊗ v`.
`tensorCompactProjection_toLinearMap` states that its linear map is exactly
`LinearMap.rTensor V Q.lower.toSubmodule.mkQ`.

- `tensorCompactProjection_finite` proves that it also intertwines the
  numerator and quotient finite tensor actions. The proof is by tensor
  induction.
- `tensorCompactProjection_surjective` is Mathlib's
  `LinearMap.rTensor_surjective`.
- `tensorCompactProjection_ker` is Mathlib's right exactness lemma
  `rTensor_mkQ`. The kernel is exactly the range of
  `LinearMap.rTensor V Q.lower.toSubmodule.subtype`, i.e. the image of the
  denominator tensored with `V`. Right exactness needs no flatness
  hypothesis, and none is used. (Over `ℂ` the coefficient module is free,
  hence flat, so this tensored inclusion is in fact injective; that fact is
  neither proved nor used in this module.)

`tensorQuotientEquiv V` is Mathlib's `rTensor.equiv` for the exact pair
`Q.lower.toSubmodule.subtype`, `Q.lower.toSubmodule.mkQ`. It is a linear
equivalence from `(Q.upper.Space ⊗[ℂ] V)` modulo that range to
`Q.Space ⊗[ℂ] V`. On the class of `f ⊗ v` it gives
`Q.projection f ⊗ v`, by definition.

`tensorHorizontalProjection τ q` postcomposes the horizontal maps of the
numerator with `tensorCompactProjection τ`. It is an intertwiner of the
horizontal finite adelic representations, by the finite equivariance above.
Its application lemma evaluates it pointwise. No surjectivity or kernel
statement is made for horizontal spaces.

## Whole-operator quotient intertwiners and equivalences

For a whole-operator quotient intertwiner
`L : Q.representation.IntertwiningMap T.representation`,
`compactRestrictionMap L` is the same linear map, viewed as an intertwiner of
the quotient compact actions. It uses the intertwining property on
`compactOperator F n k`. For a quotient equivalence `e : Q.Equivalence T`,
`Equivalence.compactRestriction e` is the compact equivalence with linear
equivalence exactly `e.toLinearEquiv`. Both application lemmas evaluate
them as `L` and `e`.

For a compact coefficient intertwiner `A : τ.IntertwiningMap υ`, with `υ` on
`W : Type w` in a further independent universe,
`tensorCompactMap L A` is the tensor product of `compactRestrictionMap L` and
`A`. It sends `f ⊗ v` to `L f ⊗ A v`. `tensorCompactMap_finite` proves finite
equivariance by tensor induction and the intertwining property of `L` on
`finiteOperator F n d`. `tensorHorizontalMap q L A` postcomposes with it and
is an intertwiner of the horizontal finite adelic representations.

For `e : Q.Equivalence T` and a compact coefficient equivalence
`a : τ.Equiv υ`, `tensorCompactEquiv e a` uses the genuine tensor linear
equivalence `TensorProduct.congr e.toLinearEquiv a.toLinearEquiv`.
`tensorHorizontalEquiv q e a` uses the published
`ArchimedeanGL.horizontalCoefficientEquiv`. The final application lemma
identifies it pointwise with the same tensor linear equivalence.

## Provenance and scope

Provenance is internal. The constructions are derived from the published
`OperatorSubquotient`, `OperatorSubquotientArchimedean`, `TensorHorizontal`
and `ArchimedeanHorizontal` modules. They also use Mathlib's
`Representation.tprod`, `Representation.IntertwiningMap.tensor`,
`TensorProduct.congr`, full-group representation invariants and the
right-exactness results of `Mathlib.LinearAlgebra.TensorProduct.RightExactness`.
No identification with an external source or normalization convention is
asserted.

Here `τ` is an explicit complex representation of the abstract group `K`. It
is not asserted to come from an algebraic group representation. This module
constructs no topology, smoothness or differentiability on the tensor or
horizontal spaces. It also provides no tensor Lie action, relative
differential, cycles, boundaries or cohomology. It does not construct a
`(g, K)`-module structure, select irreducible archimedean factors, or prove
admissibility, nonvanishing, local Langlands attachments or automorphic
existence.
