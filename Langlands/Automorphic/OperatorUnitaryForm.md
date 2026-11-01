# Positive forms on actual automorphic operator realizations

This internal construction defines and transports a positive definite Hermitian
form on the existing actual `OperatorRealization F n`. The number field has
arbitrary universe, the matrix rank is any natural number, and the coefficient
field is the complex numbers.

The helper `OperatorUnitaryFormCore` packages a form for two monoid actions
and a family of linear operators on one module, with independent universes
for the module, both monoids and the operator index. The automorphic
`UnitaryForm` is its exact specialization to the existing actual carrier,
finite action, standard infinite compact action and real Lie differential.

`OperatorRealization.UnitaryForm` contains a `finiteForm`, the published
`Langlands.InvariantPositiveForm` for the actual finite adelic representation.
It retains that form's complex inner-product core: conjugate linearity in the
first argument, linearity in the second, Hermitian symmetry, nonnegativity and
definiteness. Two additional requirements use the same form:

- Every actual standard infinite compact translation preserves it.
- For every element `X` of the actual real archimedean matrix Lie algebra,
  the differential operator `D_X` satisfies
  `B(D_X f, g) + B(f, D_X g) = 0`.

Here `D_X` is the existing restricted enveloping action applied to the
enveloping generator of the complexification of `X`. Thus the differential
condition concerns the already constructed genuine matrix-coordinate
directional derivative. It is imposed for real directions; complex scalar
multiples of these generators are not required to be skew Hermitian.

`OperatorRealization.IsUnitarizable` says that such a form exists on this
actual realization. It is distinct from the generic
`Langlands.IsUnitarizable` applied to a monoid representation. In particular,
the whole concrete complex operator algebra is not required to preserve the
form: its nonunitary scalar operators would make that requirement unsuitable.
Finite translations and compact translations preserve the form, while real
differential generators satisfy the displayed infinitesimal equation.

`UnitaryForm.compactForm` retains exactly the same positive form for the
actual compact representation. The `finiteForm` already provides the finite
restriction. `UnitaryForm.comap` pulls a form back along any injective
intertwiner of the entire operator algebra. Its value is
`B(L f, L g)`. The published finite-form pullback proves all inner-product
core conditions and finite invariance. Applying the same form to the compact
intertwining identities proves compact invariance. Applying the sum of the
two inner-product expressions to the differential intertwining identities
proves the skew equation. Injectivity
ensures definiteness. `ofEquivalence` specializes this to a genuine
whole-operator equivalence.

The accompanying proofs show preservation along an injective intertwiner and
preservation and reflection along an equivalence. Forgetting conditions yields
the existing generic unitarizability predicates for the actual finite and
compact restrictions. The finite equivalence transports this result to the
actual embedded finite form image. Finally the equivalence invariance descends
the predicate to the existing whole-operator `IsoClass`; on the class of an
actual representative it is exactly the representative's predicate.

The provenance is internal: this pair combines the published algebraic
positive-form infrastructure with the published actual finite, compact and
real differential operators and their full intertwiners. It makes no new
original-literature identification. There is no norm, continuity condition on
the form, Hilbert completion, unitary globalization, invariant integral
formula, occurrence theorem or universal unitarizability assertion. No
existence of such a form for an arbitrary actual realization is supplied.
Subquotient unitarizability is not asserted.
