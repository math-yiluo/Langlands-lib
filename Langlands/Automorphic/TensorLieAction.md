# Diagonal Lie actions on actual automorphic tensors

This internal construction combines the actual differential action on
`OperatorRealization.Space` with an explicitly supplied coefficient Lie module.
It applies to a number field `F : Type u`, every natural rank `n`, actual
realizations `S` and `T`, and complex vector spaces `V : Type v` and `W : Type w`.
The field and coefficient universes are independent. Neither positive rank nor
finite coefficient dimension is required. No topology on the coefficient space
is assumed or constructed.

Write `g = ArchimedeanGL.ComplexLieAlgebra F n`. The input on `V` consists of
`AddCommGroup V`, `Module ℂ V`, `LieRingModule g V` and `LieModule ℂ g V`.
Thus a coefficient action is supplied explicitly. There is no claim here that it
has been obtained by differentiating an algebraic representation.

## Actual diagonal action and restrictions

The first tensor factor is the concrete `S.Space` of stable automorphic
functions. Its Lie module structure is the published
`OperatorRealization.complexLieRingModule` / `complexLieModule`, induced by the
actual enveloping differential operators. Mathlib's tensor Lie module instances
therefore supply a Lie module on `S.Space ⊗[ℂ] V`.

`tensorComplexLieAction` is precisely the associated
`LieModule.toEnd` homomorphism, rather than an additional assumed action. Its
pure-tensor formula, `tensorComplexLieAction_tmul`, is

```text
X · (f ⊗ v) = (S.complexLieAction X f) ⊗ v + f ⊗ [X,v].
```

The action is complex-linear in `X` and in the tensor, and satisfies the Lie
representation identity by the Mathlib tensor construction. The first summand
uses the actual differential action on the realized automorphic function.

`tensorReducedLieAction` restricts this same homomorphism along the actual
`reducedComplexInclusion`. Its domain is the complexification of the
coordinatewise real-trace kernel, retaining imaginary scalar directions at
complex places. `tensorCompactLieAction` restricts along the actual
`compactComplexInclusion`. Their application lemmas state these restrictions
pointwise. `tensorReducedLieAction_compact` proves equality of the compact
restriction directly and through `compactToReducedComplex`. It uses the
published equality of the two inclusions and imposes no new compatibility
assumption. These two declarations are explicit Lie homomorphisms; this module
does not introduce further reduced or compact Lie module instances.

## Finite adelic translation

`tensorFiniteRepresentation` is the imported finite adelic representation from
`TensorHorizontal`: translation acts on `S.Space` and trivially on `V`.
`tensorFiniteRepresentation_complexLieAction` proves that it commutes with the
whole diagonal complex Lie action. On pure tensors the first summand uses the
published commutation of finite translation and the actual differential action;
the second uses that the finite action leaves the coefficient factor alone.
Tensor induction extends the equality to all tensors, with linearity handling
addition.

`tensorFiniteLieMap` bundles each finite translation as a Lie module
endomorphism of the tensor. Its underlying linear map remains exactly
`tensorFiniteRepresentation V d`, as its application lemma states. The analogous
commutation identities for `tensorReducedLieAction` and
`tensorCompactLieAction` follow by evaluating the full identity on their actual
inclusions. No coefficient finiteness or finite-place coefficient action is used.

## Explicit compact covariance

A full compact coefficient representation
`τ : Representation ℂ (standardInfiniteCompact F n) V` may also be supplied.
The theorem `tensorCompactRepresentation_complexLieAction` has the explicit
hypothesis

```text
τ(k)[X,v] = [complexLieConjugation F n k.val X, τ(k)v]
```

for every compact group element `k`, complex Lie vector `X` and coefficient
vector `v`. Under that hypothesis, the diagonal tensor compact representation
satisfies

```text
(S.tensorCompactRepresentation τ k) (X · t)
  = (Ad(k)X) · (S.tensorCompactRepresentation τ k t).
```

The actual automorphic factor's compact covariance is already proved in
`OperatorCompactCompatibility`; the coefficient factor's covariance is exactly
the displayed hypothesis. The proof applies both identities on pure tensors and
then uses tensor induction. This is a conditional compatibility theorem for
specified actions, not a construction of coefficient covariance. In particular,
it supplies no derivative of `τ` and no identification of the compact Lie action
with differentiation of the compact group action. The compact group is the full
standard orthogonal/unitary subgroup, including its disconnected components.

## Genuine maps and equivalences

For a full operator intertwiner `L : S.Intertwiner T` and a coefficient Lie module
map `A : V →ₗ⁅ℂ,g⁆ W`, `tensorComplexLieMap L A` is Mathlib's tensor map of
`L.complexLieRestriction` and `A`. Its underlying linear map is
`TensorProduct.map L.toLinearMap A.toLinearMap`, with pure-tensor formula
`L f ⊗ A v`. `tensorComplexLieMap_finite` additionally proves finite adelic
equivariance, using `L.finite` on the first factor and tensor induction.

For a full operator equivalence `e : S.Equivalence T` and a coefficient Lie module
equivalence `a : V ≃ₗ⁅ℂ,g⁆ W`, `tensorComplexLieEquiv e a` has the genuine linear
equivalence `TensorProduct.congr e.toLinearEquiv a.toLinearEquiv` as its underlying
map. Its Lie compatibility is that of the preceding tensor Lie map, and its
pure-tensor formula is `e f ⊗ a v`. `tensorComplexLieEquiv_finite` records its
finite adelic compatibility on every tensor. Thus both its invertibility and its
Lie compatibility are implemented, and the finite compatibility is proved.

## Provenance and scope

The provenance is internal composition of published project constructions and
Mathlib. The project inputs are `OperatorLieAction`,
`OperatorCompactCompatibility`, `TensorHorizontal`, and the actual reduced and
compact inclusions imported by that chain. The Mathlib inputs are
`TensorProduct.LieModule.lieRingModule`, `lieModule`, `lie_tmul_right`, `map`,
`LieModule.toEnd`, and `TensorProduct.congr`. The tensor representation identities
are proved as described above. No new correspondence with original literature is
asserted.

This unit constructs actions and their maps on the actual tensor carrier. It
does not attach general scheme coefficients, construct their differential,
identify analytic differentiation of a compact coefficient representation,
construct a relative differential or cohomology, or establish automorphic
occurrence. Those remain separate obligations under the parent task. The supplied
coefficient Lie action and the explicit covariance hypothesis must be instantiated
by such later constructions when needed.
