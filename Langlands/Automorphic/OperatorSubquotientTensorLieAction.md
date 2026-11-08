# Diagonal Lie actions on actual automorphic operator quotient tensors

This internal construction is the quotient analogue of the published module
`TensorLieAction`. It works with every number field `F : Type uF`, every
natural rank `n` and an actual `Q : OperatorSubquotient F n`. The carrier of
the first factor is the original module quotient
`Q.Space = Q.upper.Space ⧸ Q.lower.toSubmodule`. Its denominator is already
invariant under the whole concrete automorphic operator algebra. No further
invariance, covariance or finiteness hypothesis is supplied. Neither positive
rank nor finite coefficient dimension is required, and no topology on the
coefficient space is assumed or constructed.

Write `g = ArchimedeanGL.ComplexLieAlgebra F n`. The coefficient input is a
complex vector space `V : Type v` with `AddCommGroup V`, `Module ℂ V`,
`LieRingModule g V` and `LieModule ℂ g V`. Thus the coefficient Lie action is
supplied explicitly. Nothing here claims that it comes from differentiating an
algebraic or compact group representation. A second coefficient module
`W : Type w` and a second quotient `T` occur in the map section. The field and
coefficient universes are independent.

The declarations are in `Langlands.Automorphic.OperatorSubquotient`.

## Actual diagonal action and restrictions

The Lie module structure on `Q.Space` is the published
`OperatorSubquotient.quotientComplexLieRingModule` / `quotientComplexLieModule`
from `OperatorSubquotientLieAction`. It is given by `Q.complexLieAction`, the
quotient's induced enveloping action `Q.envelopingAction` composed with
`envelopingGenerator`. Mathlib's tensor Lie
module instances therefore supply a Lie module on `Q.Space ⊗[ℂ] V`.

`tensorComplexLieAction V` is exactly the associated `LieModule.toEnd`
homomorphism; no further action is assumed. Its pure-tensor formula,
`tensorComplexLieAction_tmul`, is

```text
X · (f ⊗ v) = (Q.complexLieAction X f) ⊗ v + f ⊗ [X,v].
```

`tensorReducedLieAction V` restricts this same homomorphism along the actual
`reducedComplexInclusion`, and `tensorCompactLieAction V` restricts it along the
actual `compactComplexInclusion`. Their application lemmas state these
restrictions pointwise. `tensorReducedLieAction_compact` shows that restricting
through `compactToReducedComplex` gives the compact restriction. The proof applies
the published equality `reducedComplexInclusion_compact` of the two inclusions;
it adds no compatibility assumption. No additional reduced or compact Lie module
instances are introduced.

## Finite adelic translation

`tensorFiniteRepresentation V` is the imported finite adelic representation
from `OperatorSubquotientTensorHorizontal`. Translation acts on `Q.Space` by
`Q.finiteRepresentation` and trivially on `V`.
`tensorFiniteRepresentation_complexLieAction` proves that it commutes with the
whole diagonal complex Lie action. The proof compares the two composite linear
maps on pure tensors (`TensorProduct.ext'`). For the first summand it uses the
published quotient commutation `finiteRepresentation_complexLieAction`; the
second summand holds because the finite action fixes the coefficient factor.

`tensorFiniteLieMap V d` bundles each finite translation as a Lie module
endomorphism of the tensor. Its underlying linear map is exactly
`tensorFiniteRepresentation V d`, as its application lemma states. The analogous
commutation identities for `tensorReducedLieAction` and `tensorCompactLieAction`
follow by evaluating the full identity on the actual inclusions.

## Explicit compact covariance

A full compact coefficient representation
`τ : Representation ℂ (standardInfiniteCompact F n) V` may also be supplied.
`tensorCompactRepresentation_complexLieAction` has the explicit hypothesis

```text
τ(k)[X,v] = [complexLieConjugation F n k.val X, τ(k)v]
```

for every compact group element `k`, complex Lie vector `X` and coefficient
vector `v`. Under that hypothesis, the diagonal quotient tensor compact
representation `Q.tensorCompactRepresentation τ` (from
`OperatorSubquotientTensorHorizontal`) satisfies

```text
(Q.tensorCompactRepresentation τ k) (X · t)
  = (Ad(k)X) · (Q.tensorCompactRepresentation τ k t).
```

The covariance on the first factor is the published quotient theorem
`compactRepresentation_complexLieAction`. The covariance on the coefficient
factor is exactly the displayed hypothesis. The proof applies both on pure
tensors, via `TensorProduct.ext'`. The result is conditional on specified actions
and does not construct coefficient covariance. In particular, it supplies no
derivative of `τ`. The compact group is the full standard orthogonal/unitary
subgroup, including its disconnected components.

## The canonical projection from the numerator tensor Lie module

`tensorComplexLieProjection V` is Mathlib's tensor Lie module map
`TensorProduct.LieModule.map` of the published quotient Lie projection
`Q.complexLieProjection` and the identity of `V`. Its source is the numerator
tensor `Q.upper.Space ⊗[ℂ] V`, which carries the Lie module of the published
`TensorLieAction` for the realization `Q.upper`. It sends `f ⊗ v` to
`Q.projection f ⊗ v`.

- `tensorComplexLieProjection_toLinearMap` states that its linear map is
  `LinearMap.rTensor V Q.lower.toSubmodule.mkQ`. Hence
  `tensorComplexLieProjection_eq_compact` identifies it, for every compact
  coefficient representation `τ`, with the linear map of the published
  `tensorCompactProjection τ`.
- `tensorComplexLieAction_projection` is its Lie compatibility: the quotient
  diagonal operator of a projected tensor is the projection of
  `Q.upper.tensorComplexLieAction V X t`.
- `tensorComplexLieProjection_finite` proves that it also intertwines the
  numerator and quotient finite tensor actions.
- `tensorComplexLieProjection_surjective` follows from Mathlib's
  `LinearMap.rTensor_surjective`.

`lowerTensorComplexLieSubmodule V` is the actual Lie submodule of the numerator
tensor whose underlying submodule is the range of
`LinearMap.rTensor V Q.lower.toSubmodule.subtype`, i.e. the image of the
denominator tensored with `V` (`lowerTensorComplexLieSubmodule_toSubmodule`
holds by definition). The denominator tensor is defined as this image, and the
constructions below use only right exactness; no flatness of `V` is invoked.
(Over `ℂ` every coefficient module `V` is free, hence flat, so this tensored
inclusion is in fact injective; that fact is neither proved nor used here.) Its
Lie closure is proved, not assumed. By Mathlib's right-exactness lemma `rTensor_mkQ`, a tensor lies in this
range exactly when its projection vanishes (`mem_range_rTensor_lower_iff`,
`mem_lowerTensorComplexLieSubmodule`). The projection is a Lie module map, so
this condition is preserved by every Lie operator. Consequently
`tensorComplexLieProjection_ker` states that the Lie kernel of the projection is
exactly `lowerTensorComplexLieSubmodule V`.

`tensorComplexLieQuotientEquiv V` is an equivalence of Lie modules over `g`
from Mathlib's Lie quotient
`(Q.upper.Space ⊗[ℂ] V) ⧸ lowerTensorComplexLieSubmodule V` to
`Q.Space ⊗[ℂ] V`. Its linear equivalence is
`Submodule.quotEquivOfEq` followed by the published `tensorQuotientEquiv V`, which
is Mathlib's `rTensor.equiv`. Its Lie compatibility is that of the projection on
representatives. `tensorComplexLieQuotientEquiv_mk` identifies the class of every
numerator tensor `t` with `tensorComplexLieProjection V t`.

## Whole-operator quotient intertwiners and equivalences

For a whole-operator quotient intertwiner
`L : Q.representation.IntertwiningMap T.representation`,
`complexLieRestrictionMap L` is the same linear map, viewed as a Lie module map
of the quotient complex Lie modules. Its Lie compatibility is the intertwining
property on `differentialOperator F n (envelopingGenerator F n X)`.

For a coefficient Lie module map `A : V →ₗ⁅ℂ,g⁆ W`, `tensorComplexLieMap L A` is
Mathlib's tensor Lie map of `complexLieRestrictionMap L` and `A`. It sends
`f ⊗ v` to `L f ⊗ A v`. `tensorComplexLieMap_finite` proves finite adelic
equivariance from the intertwining property of `L` on `finiteOperator F n d`.

For `e : Q.Equivalence T` and a coefficient Lie module equivalence
`a : V ≃ₗ⁅ℂ,g⁆ W`, `tensorComplexLieEquiv e a` has the genuine linear equivalence
`TensorProduct.congr e.toLinearEquiv a.toLinearEquiv` as underlying map. Its Lie
compatibility is that of `tensorComplexLieMap e.toIntertwiningMap a.toLieModuleHom`.
Its pure-tensor formula is `e f ⊗ a v`, and `tensorComplexLieEquiv_finite`
records finite adelic compatibility on every tensor.

## Provenance and scope

Provenance is internal. The constructions are derived from the published
`OperatorSubquotientLieAction`, `OperatorSubquotientTensorHorizontal` and
`TensorLieAction` modules and the actual reduced and compact inclusions they
import. The Mathlib inputs are `TensorProduct.LieModule.lieRingModule`,
`lieModule`, `lie_tmul_right` and `map`, together with `LieModule.toEnd`,
`TensorProduct.congr`, Lie submodules and quotients, and the right-exactness
results of `Mathlib.LinearAlgebra.TensorProduct.RightExactness`. No
identification with an external source or normalization convention is asserted.

This unit constructs Lie actions and maps on the actual quotient tensor carrier.
It provides no coefficient group action derived from the Lie action, no
differentiation of `τ` and no relative differential, cycles, boundaries or
cohomology. It also constructs no `(g, K)`-module structure and selects no
irreducible archimedean factors. It proves no admissibility, nonvanishing, local
Langlands attachments or automorphic existence. These remain separate obligations
under the parent task. The coefficient Lie action and the covariance hypothesis
must be instantiated by such later constructions when needed.
