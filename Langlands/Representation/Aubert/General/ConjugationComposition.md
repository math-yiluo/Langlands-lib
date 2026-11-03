# Composition and inner comparisons for actual conjugation transport

Worker 55, task `fc414cb1-5832-4033-a2aa-d7c27f5e4691`, revision 1.

This is an internal construction derived from the published
`Langlands.Aubert.General.conjugationEquiv` and `conjugationFunctor` in
`Langlands.Representation.Aubert.General.Parabolic`. It implements the algebraic
transport step needed when composing association witnesses. It does not prove
existence or uniqueness of cuspidal support or produce a torus normalizer.

For an arbitrary topological group `G : Type uG`, subgroups `M`, `N`, `L`, and
independent representation carrier universe `uV`, membership data
`x ∈ N ↔ g⁻¹ * x * g ∈ M` define the actual transport `c_g` with action
`x ↦ A(g⁻¹ x g)`. No local compactness, irreducibility, finite length or
admissibility assumption is used.

`conjugationMembership_inv`, `conjugationMembership_mul` and
`conjugationMembership_inner` give the actual subgroup equivalences for inverse,
product and inner representatives. The product order is `f * g` for transport
first by `g` and then by `f`.

`conjugationFunctorCompIsoApp` compares `c_f(c_g(A))` with `c_(f*g)(A)` by the
identity linear equivalence. Its proof identifies the subgroup elements
`g⁻¹(f⁻¹ x f)g` and `(f*g)⁻¹ x (f*g)` using associativity. The natural
isomorphism `conjugationFunctorCompIso` has these components; naturality is
equality of the unchanged underlying linear maps.

`conjugationFunctorInvIsoApp` compares `c_(g⁻¹)(c_g(A))` with `A` by the identity
linear map, using cancellation in `G`.

`conjugationFunctorInnerIso` compares `c_m(A)` with `A` for an actual `m : M`.
Its underlying linear equivalence is `A(m)` with inverse `A(m⁻¹)`, obtained from
`Representation.asGroupHom` and `LinearMap.GeneralLinearGroup.toLinearEquiv`.
The intertwining identity is `A(m) A(m⁻¹ x m) = A(x) A(m)`.

Finally, `conjugationDataIsoTrans` and `conjugationDataIsoSymm` construct actual
isomorphisms of transported data by applying a conjugation functor to a given
isomorphism and composing the preceding comparisons. They retain exactly the
product or inverse element used in the subgroup membership proof. These are
constructions in the full smooth category, with no passage to a Grothendieck
group or isomorphism class and no external structural assumptions.
