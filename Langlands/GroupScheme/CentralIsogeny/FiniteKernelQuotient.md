# Finite central quotients from actual finite kernels

Author: Worker 1487.

This internal deduction constructs finite central isogenies using the existing
normal-subgroup quotient theorem. It retains the actual kernel and its point
functor on every relative scheme test, including nonreduced tests.

For any base scheme, `isFinite_of_finite_kernel` proves that a flat, surjective,
quasi-compact group homomorphism with finite scheme-theoretic kernel is finite.
The actual kernel-pair square identifies the pullback of the homomorphism along
itself with the projection from the source times the kernel. That projection is
a base change of the finite structure morphism of the kernel. Finiteness then
descends along the given fpqc homomorphism by the published fpqc finite descent
result.

`RelativeRoot.IsFppfQuotient.isFinite_of_finite_subgroup` applies this argument
to a specified finite subgroup whose inclusion is monomorphic and whose full
range functor is the kernel of the quotient. The existing uniqueness theorem
for representing group schemes identifies this subgroup with the actual
kernel, transferring its finite structure morphism. No smoothness or reducedness
of the kernel is needed.

If the subgroup is central,
`RelativeRoot.IsFppfQuotient.isCentralIsogeny_of_finite_subgroup` also transfers
centrality along the full kernel range equality. Flatness, surjectivity and
local finite presentation are the existing fppf quotient properties. Together
with the proved finiteness these give the Library's actual `IsCentralIsogeny`.

`exists_centralIsogeny_of_finite_central_subgroup` starts with a smooth affine
group over an arbitrary field and a finite central normal closed subgroup.
The normal-subgroup quotient theorem gives a smooth affine quotient. Affineness
makes its projection quasi-compact, so the preceding result proves that this
projection is a central isogeny with exactly the specified full kernel functor.
`FiniteCentralSubgroupQuotientStatement.{u}` packages this exact universal
assertion, and `finiteCentralSubgroupQuotient` proves it. Normality remains an
explicit hypothesis in this wrapper. The centre and kernel need not be smooth. The field need not be perfect,
infinite or algebraically closed.

This unit is derived from the existing kernel-pair construction, uniqueness of
represented subgroup schemes, fpqc finiteness descent and normal-subgroup
quotients. It proves neither decrease of geometric torus weights nor termination
of an isogeny construction and does not complete the no-torus theorem.
