# Scalar actions on an unchanged Hilbert completion

This is an internal construction from the published invariant positive forms,
scalar twists and actual uniform completions in
`Langlands.Representation.Unitary.{Basic,Twist,Completion}`. It makes no new
identification with an original-literature theorem.

Let `G`, `H` and `V` have independent universes, with both groups arbitrary and
`V` a complex module with an additive commutative group. Fix a representation
`ρ` of `G` on `V` and an actual `InvariantPositiveForm ρ`, denoted `b`. No
topology, finite-dimensionality or completeness of `V` is required.

For `θ : H →* ℂˣ` and a proof that every `θ h` has norm one,
`b.scalarActionForm θ hθ` is an invariant positive form for
`twist θ (Representation.trivial ℂ H V)`. This representation acts by
`v ↦ (θ h : ℂ) • v`. The construction first puts `b`'s exact
`toInnerProductCore` on the trivial action and then applies the published
unit-modulus twist construction. Its positivity and invariance are therefore
proved by those constructions.

The new form retains the original core definitionally. Consequently its
form-dependent normed carrier, norm, topology, Hilbert completion and canonical
embedding are the same as those of `b`, with no comparison isomorphism.
`scalarActionForm_inner` and `scalarActionForm_toHilbert` record the unchanged
inner product and embedding.

`completedOperator_eq_smul` has a separate useful scope: if one original
operator `ρ g` equals multiplication by any specified `z : ℂ`, its completed
operator is multiplication by the same `z`. Both sides are continuous, their
equality set is closed, and the published formula on the dense canonical image
reduces the claim to the original operator identity and linearity of
`toHilbert`. There is no unit-modulus premise in this lemma; invariance is
already part of `b`. `scalarActionForm_completedOperator` specializes it to the
new scalar representation.

If `H` has any topology for which `h ↦ (θ h : ℂ)` is continuous,
`scalarContinuousAction` packages

`(h, x) ↦ (b.scalarActionForm θ hθ).completedRepresentation h x`

as a continuous map `H × b.HilbertCompletion → b.HilbertCompletion`.
The completed scalar formula identifies it with `(h, x) ↦ (θ h : ℂ) • x`;
continuity follows from the character and continuous scalar multiplication.
No topological-group, smoothness or finite-orbit hypothesis is needed here.
`scalarContinuousAction_apply` gives the scalar formula. The representation
laws, inverse operators and preservation of norm and inner product remain
those of the published actual completed representation.

Two algebraic helpers avoid unfolding concrete function carriers.
`operator_eq_smul_of_scalarEquiv` takes a linear equivalence `e : ℂ ≃ₗ[ℂ] V`
and an operator satisfying `a (e c) = e (z * c)` for all `c`; surjectivity and
linearity of `e` prove `a v = z • v` for every vector.
`scalarEquiv_right_translation` takes any map `j : V → H → ℂ` satisfying
`j (e c) h = (θ h : ℂ) * c`. It proves
`j ((θ g : ℂ) • v) x = j v (x * g)` by the same surjectivity reduction,
character multiplicativity and commutativity of complex multiplication.
The latter lemma requires neither linearity of `j` nor evaluation continuity.

This module supplies an additional scalar action on a supplied positive core.
It does not construct a positive form for an arbitrary representation, prove a
general globalization theorem, compare the form topology with a function-space
topology, or extend differential operators.
