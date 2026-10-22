# B-linear similitudes and isomorphisms with a line-valued form

This is a derived algebraic interface for the isomorphisms used in PEL level
structures. It constructs the groups and their actions from actual linear
equivalences and bilinear forms. The geometric Tate modules, their Weil pairing,
and the geometric monodromy representation are separate constructions.

## Inputs and groups

Let R be a commutative ring, B a ring, V and W additive commutative groups with
R-module and B-module structures, and L an R-module. Write
ψ : V × V → R and φ : W × W → L for the two R-bilinear forms.
The general construction does not require that L already be free of rank one.
When a compatible isomorphism exists, its compatibility condition entails the
existence of an R-linear equivalence R ≃ L.

`bilinearSimilitudes B ψ` is the subgroup of
Aut_B(V) × Rˣ consisting of pairs (g,c) satisfying
ψ(gx,gy) = c ψ(x,y). Multiplication is composition of the linear maps and
multiplication of the scalars. The subgroup proof establishes the identity,
product and inverse conditions directly from the displayed equation.
`bilinearSimilitudes.underlying` and `multiplier` are the two homomorphisms.
The multiplier is retained as a coordinate; forgetting it is proved injective
when there exist x,y with ψ(x,y)=1. No uniqueness is asserted for arbitrary
degenerate forms.

`twistedSimilitudes B φ` is the subgroup of Aut_B(W) × Aut_R(L) whose members
(a,d) satisfy φ(ax,ay)=d(φ(x,y)). Thus the action on the value module is part of
the group element. Its identity, product and inverse conditions are also proved.

For a specified `Langlands.Shimura.AlgebraInvolution R B`, the proposition
`FormRespectsInvolution` means ψ(bx,y)=ψ(x,σ(b)y). This reuses the published
involution definition. In the PEL specialization, B is an R-algebra and the
R-module structures are its scalar restrictions; one imposes the alternating,
nondegenerate and involution compatibility conditions and the stated dimension
and faithfulness hypotheses. These restrictions are unnecessary for the group
and action constructions and are not asserted by this module.

## Compatible isomorphisms and the twist

`FormCompatible ψ φ η`, for a B-linear equivalence η : V ≃ W, means that
there exists an R-linear equivalence t : R ≃ L with
φ(ηx,ηy)=t(ψ(x,y)) for every x,y. `FormIso B ψ φ` is the subtype of those η.
A choice of t is a proposition witness, not a coordinate of a level datum.
There is no chosen basis of L, system of roots of unity, or trivial monodromy
action on L in the definition.

`scalarEquivUnit` constructs the unit corresponding to a linear automorphism
of R by evaluating it and its inverse at 1. Linearity proves that the
automorphism is multiplication by this unit. Using this construction,
`formCompatible_iff` proves that, relative to any specified trivialization t₀,
compatibility is equivalent to the existence of c ∈ Rˣ such that
φ(ηx,ηy)=t₀(c ψ(x,y)). Thus the existential-trivialization definition has exactly
the intended up-to-unit meaning when a trivialization is used for comparison.

## Actions

`FormIso.precomp η g` is η ∘ g, using the underlying linear map of a source
similitude. If t witnesses compatibility of η and c is the multiplier of g,
then the composite of multiplication by c with t witnesses compatibility of
η ∘ g. The proved identity and composition laws are
(η ∘ g) ∘ h = η ∘ (g h), where the automorphism product acts by g(h(x)).
This gives a left action of the opposite source similitude group.

`FormIso.postcomp (a,d) η` is a ∘ η. Its compatibility witness is d ∘ t,
which explicitly retains the transformation of the form's value module.
These maps give a left action of `twistedSimilitudes B φ`. Associativity proves
that the two actions commute, providing the `SMulCommClass` instance required
by the published `InvariantOrbits` construction. In an application a monodromy
homomorphism into this target group supplies the left action to restrict.
The module itself does not claim that this target group is a fundamental group.

`FormIso.exists_precomp_eq` proves that any two compatible isomorphisms differ
by a source similitude: use η⁻¹ ∘ ξ and the unit comparing their trivializations.
`FormIso.precomp_injective` proves freeness when ψ takes the value 1, by
cancelling η and using uniqueness of the multiplier. Neither result asserts
nonemptiness of the isomorphism set.

## Provenance and remaining specialization

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Section III.1, printed p.91 (PDF p.99), defines the invariant orbit of
B ⊗ A_f-linear isomorphisms compatible with the polarization pairing up to a
unit, and gives the right action η ↦ η ∘ g. Kottwitz, *Points on some Shimura
varieties over finite fields* (1992), Section 5, printed pp.390–391 (PDF
pp.18–19), explains the twist-valued pairing, the up-to-scalar convention,
simple transitivity when the isomorphism set is nonempty, and the commuting
left monodromy and right similitude actions. The arbitrary-ring interface here
is derived from those constructions; neither source presents this Lean
abstraction. The intrinsic proofs above justify its broader algebraic scope.

The existing `AlgebraInvolution.similitudes` construction uses units in an
algebra with an involution. The present group instead uses B-linear
automorphisms of a bilinear space. Identifying them in the Harris specialization
requires constructing the relevant adjoint involution and proving the
identification; no such identification is assumed or proved here. This unit
also does not construct scalar extension to finite adeles, its topology,
compact open subgroups, actual Weil pairings or Tate twists, or geometric
monodromy. Those remain obligations of the parent task. In particular this is
an algebraic prerequisite, not the completed geometric PEL level construction.
