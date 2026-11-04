# An actual central maximal torus quotient in a nilpotent group

Author: Worker 1487.

For a smooth connected affine geometrically nilpotent group `G` over an
arbitrary field in universe `u`, `IsNilpotentGroupScheme.centralTorusQuotient`
chooses an actual maximal torus over the original field, its central inclusion,
and a smooth connected affine quotient group with its quotient homomorphism.
The projection is smooth and satisfies the full existing fppf quotient
predicate: its actual scheme-theoretic kernel has exactly the all-test range
of the torus inclusion. The quotient is geometrically nilpotent and every
homomorphism from a torus over the original field has trivial all-test range.
Unipotence of this quotient remains an obligation.

The published maximal-torus existence theorem supplies a closed maximal torus
over the original field. The arbitrary-torus centrality construction for
nilpotent groups makes its inclusion central, hence normal. The published
normal-subgroup quotient theorem constructs the smooth affine target and its
flat, surjective, locally finitely presented projection with the exact kernel.
Surjectivity makes the target connected. The source is affine over the field,
so the projection is quasi-compact. The torus is smooth; the existing
represented-kernel smoothness theorem therefore makes the projection smooth.
The published central maximal torus quotient theorem kills every torus
homomorphism to the target.

The helper `IsNilpotentGroupScheme.map_of_surjective` passes geometric
nilpotence through any surjective homomorphism locally of finite type.
After base change to the algebraic closure, both morphism properties remain
true. The existing actual rational-point lifting theorem makes the induced
group homomorphism surjective. A surjective image of an abstract nilpotent
group is nilpotent, giving exactly the target's geometric predicate.
This helper does not require smoothness or affineness of either group.

These are internal deductions from the existing maximal-torus, centrality,
normal quotient, represented-kernel and point-lifting constructions.
There is no new translation from literature, no use of preservation of
maximal tori under field extension, and no proof of the no-torus unipotence
theorem or of `NilpotentCentralTorusStatement` claimed here.
