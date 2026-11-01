# Left exactness of actual pseudo-F and right exactness of actual P

Workers 321 and 633 prove the published closed proposition
`Langlands.Algebra.NondegeneratePInductionExactnessTheorem`, without modifying
that statement or any of its imported Lean and Markdown pairs. This is the
P/pseudo-F portion of Renard I.2.4.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The theorem and proof are printed pp.18–19 / PDF24–25. The original module
conventions are printed pp.5–7 / PDF11–13; the tensor and Hom constructions
are printed pp.15–18 / PDF21–24; the exactness conventions are printed
pp.266–267 / PDF272–273. The registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was consulted at PDF1–2 and PDF18–19. Its PDF1 confirms the direction
P left adjoint to pseudo-F. The implemented proof uses concrete kernels
and cokernels.

The helper
`RenardHomFunctors.pseudoF_sequenceLeftExact` proves the left assertion.
For the actual regular left B-module B, the ambient Hom functor preserves
kernels: a family of B-linear maps killed by postcomposition lifts pointwise
into the concrete subtype kernel. Evaluating the original family identities
proves that the lift is additive and A-linear, and the kernel inclusion proves
uniqueness. Additivity converts kernel preservation to preservation of finite
limits. The published exactness of the inclusion of nondegenerate modules and
the nondegenerate-part functor supplies their finite-limit preservation.
The published equality expressing pseudo-F as their composite with ambient Hom
then gives its full `SequenceLeftExact` predicate.

The helper `NondegeneratePInductionRightExactness.sequenceRightExact`
proves the right assertion directly for every exact short complex with an
epimorphic right boundary. The published exact inclusion transfers exactness
to the ambient original module category. Its epimorphism is surjective on the
original additive carriers, using the published equivalence with modules over
the integer unitization. The concrete exactness criterion identifies the range
of the first map with the kernel of the second.

Given a morphism out of the middle P-object that kills the first tensor map,
the published original-action tensor-Hom curry produces a map on the original
middle module. The range/kernel equality shows that it kills the kernel of the
surjection. Additive surjective descent then produces a map on the last module;
lifting elements along the surjection proves its A-linearity. The published
uncurry returns the required map out of the last P-object. Equality on pure
tensors proves factorization and uniqueness. Thus the mapped right boundary is
a cokernel, which gives both mapped exactness and its epimorphism. The argument
uses the published generic additive curry/uncurry proof, without introducing a
new generic exactness theorem.

Both helper developments are restricted to the actual additive carrier B and
its regular left B-action. They are internal derived arguments accompanying
this closed proof. They do not assert a generic tensor/Hom theorem or an
actual categorical adjunction. Published prerequisites are imported by their
Lean names.

The final theorem quantifies over the original independent universes
`uA`, `uB` and `v`, with target carrier exactly `max uB v` for both functors.
Its inputs are precisely the idempotentedness of A and B, the specified
right A-action on B, commutation with the regular left B-action, and the
nondegeneracy of that specified bimodule. The proof introduces these inputs
and combines the two helper conclusions. The sequence predicates use exactly
the named `NondegenerateModuleCat.abelian` structures in the published target.
They cover every exact short complex with the respective initial mono or final
epi, and preserve both exactness and that boundary map.

This is an internal arbitrary-ring additive generalization of Renard's
complex-algebra setting. It imposes no nontriviality, unit-action, coefficient
action or comparison between the three universes. Zero rings and trivial
nondegenerate modules are included. Complex-linearity, coefficient and scalar
comparisons, unitization, the F/I assertions and injectivity remain separate
obligations. This proof does not complete all of I.2.4 or the whole book.
