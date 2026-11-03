# Natural character actions and their grading

This internal prerequisite converts natural actions of a diagonalizable character
functor on affine algebra-valued points to group-algebra coactions. The point action
need not preserve any group law on the affine target, so this formulation is
suitable for twisted transporter actions as well as conjugation.

The structure `CharacterAction.Action` records an action of `Hom(M,Aˣ)` on the
`A`-points `Hom_R(B,A)` of `Spec B`, natural in every commutative `R`-algebra `A`.
The coaction is its value at the universal character over `B[M]` and the constant
map from `B`. Evaluation recovers the action at any character and any point.
`coefficientMap` gives the group-algebra map that applies a homomorphism to every
coefficient, with a proved coefficient formula.

The diagonal map sends `single m b` to `single m (single m b)` in `B[M][M]`.
Applying naturality twice and then the action's multiplication law proves that
applying the coaction to every coefficient of the coaction agrees with this
diagonal map. Taking the outer coefficient of degree `m` shows that each
coefficient of the coaction is homogeneous of degree `m`. The algebra-homomorphism
law puts scalars in degree zero. The identity action also gives the counit
identity.

`formallySmooth_fixedQuotient` applies
`GradedFixedQuotient.formallySmooth_quotient_fixedIdeal` to these two identities:
if `B` is formally smooth over `R`, then the quotient of `B` by the coefficients
of `coaction(b) - single 0 b` is formally smooth over `R`. There is no field,
characteristic, finite-rank, or finite-type assumption in this algebraic result.

`IsFixed a x` means that a point `x : B ⟶ C` is fixed by every character after
every `R`-algebra refinement `C ⟶ D`.
`fixedIdeal_le_ker_iff_isFixed` proves that this property is equivalent to the
fixed ideal lying in the kernel of `x`. In the forward direction, the kernel
criterion gives the coefficient-wise fixed identity over `C[M]`; evaluating it
at any refinement and character gives the required action equality. Conversely,
fixedness at the universal character over `C[M]` gives the coefficient-wise
identity and hence containment of the full fixed ideal in the kernel.

This module does not construct an action from a group-scheme morphism, descend
affine fixedness to arbitrary test schemes, or assert geometric smoothness.
Those comparison and finiteness steps remain separate prerequisites for the
torus normalizer theorem. The result applies to any action satisfying the stated
intrinsic point-action laws, including actions that do not preserve a target
group law.

This is derived internal coordinate infrastructure for fixed-locus smoothness.
It uses the Library's actual diagonalizable group algebra and its universal
monomial character, rather than postulating a grading for an arbitrary action.
The mathematical context is Milne, *Algebraic Groups* (2017), Theorem 13.1,
printed p.254 / PDF p.270, registered source `milne-2017-algebraic-groups`.
The published Chapter 13 errata have been read. This coordinate construction is
an alternative to the local-ring argument printed in that source.
The imported fixed-quotient lifting theorem generalizes Worker 1131's rank-one
argument; that contribution's paired Markdown records the attribution.
