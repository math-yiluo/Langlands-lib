# Actual rational generation and ambient images of Weil-restricted SU3

This internal derived unit concerns the actual affine Weil restriction
`WeilSchemeModel.groupScheme F k L` of `SU3(L/k)`, for fields in an arbitrary
common universe, a finite dimensional extension `k/F` and a separable quadratic
extension `L/k`. It has no characteristic restriction and requires neither a
separability assumption on `k/F` nor a chosen `F`-algebra structure on `L`.
The constructions derive from `SU3WeilDynamics`, `SU3RationalPoints` and
`SU3AmbientGeneration`; no additional external mathematical input is used.

The rational coefficient evaluation retains the actual nested tensor algebras.
First `rationalIntermediateEquiv` evaluates `k ⊗[F] Γ(Spec F)` to `k` using
the affine section equivalence and the right tensor unit. Next
`rationalSectionEquiv` evaluates the sections of its actual intermediate spectrum.
Finally `rationalCoefficientEquiv` evaluates the outer tensor product with `L`.
The involution compatibility is proved by tensor induction: on pure tensors it
is the `k`-linearity of the quadratic conjugation, and it respects sums.

`rationalMatrixEquiv` composes actual rational-to-affine points, the all-test
restricted SU3 comparison, and that involution-compatible coefficient evaluation.
It therefore identifies the rational points of the constructed restricted scheme
with the original determinant-one Hermitian matrices over `L`.
`rationalPointsEquiv` further identifies these with the original scheme's actual
`k`-rational points. The upper root homomorphism is the original coupled upper
matrix transported through the inverse matrix equivalence, and the point
comparison preserves it exactly.

The upper root family belongs to the actual upper subgroup functor. The proof
uses surjectivity of the involution-compatible parameter equivalence, comparison
on the ground affine test, and the inverse of the actual base-test isomorphism.
The all-test contraction of `SU3WeilDynamics` then shows that these actual rational
upper points contract under the actual transferred ground-field cocharacter.

The upper family normally generates the whole rational group. This follows by
pulling a normal subgroup back through `rationalPointsEquiv.symm`, applying the
original SU3 normal-generation theorem, and using the inverse equivalence.
For a morphism from the constructed restricted group into any target, the same
argument applied to a normal target subgroup's inverse image proves full image
containment whenever that subgroup contains the composed upper dynamics.
If the target is connected reductive, the existing dynamic-to-parabolic theorem
puts these dynamics in its actual `parabolicElementarySubgroup`; consequently
the whole rational image lies in that subgroup.

Source smoothness and reductivity, comparison of general rank-one factors with
this actual model, general classification and unrestricted local Kneser–Tits
remain separate obligations. This unit asserts the ambient containment for
the specified actual Weil-restricted SU3 source.
