# The affine adjoint Weil restriction theorem

Worker 632, with Worker 5254's Weil-pair descent, abelian-image triviality and
projection injectivity; Worker 634's pinned component comparison; Worker 47's
normal-idempotent reduction and uniqueness construction; and Worker 96's
almost-simple field-ascent argument.

`affineAdjointWeilRestriction` proves exactly
`Langlands.GroupScheme.AffineAdjointWeilRestrictionStatement.{u}` in every
universe, with no additional hypotheses. The target pair and its imported
pairs are unchanged.

The proof first supplies normal-idempotent rigidity for Weil restrictions.
Worker 47's `WeilFactor.weilFactorIdempotentRigidity_of_inputs` takes the
relative almost-simple normal-idempotent theorem and the triviality theorem
for homomorphisms with commuting image from semisimple Weil restrictions.
Both inputs are proved in the imported modules. The relative theorem retains
the original coefficient algebras and quotient formulas, including
nonreduced algebras. Its proof uses actual smooth retract geometry on
complementary opens, followed by the clopen/idempotent correspondence and
projection injectivity. The abelian-image theorem uses fppf-local perfectness,
graph idempotents after a finite-etale splitting cover, and point separation.

Worker 5254's `affineWeilPairEtaleDescent` then combines this rigidity with the
proved finite-etale chart-algebra descent theorem. Its actual coefficient
algebra and closed factor group descend, with their reductivity and
almost-simple geometric fibres, to produce generic pair descent.

Finally `affineAdjointWeilRestriction_of_descent_rigidity` applies these two
proved statements. Its existence construction uses actual products of the
relative root-component groups on further etale pinned charts. The published
affine split isomorphism theorem supplies the comparisons on those charts.
Full centre triviality makes the descended factors adjoint; the local field
comparisons give their almost simplicity. Pair descent produces the finite,
projective, etale, surjective coefficient algebra and the actual Weil
restriction isomorphism. Factor rigidity also supplies the algebra
isomorphism and actual base-change group isomorphism required for uniqueness.

## Scope and source

The theorem proved is the published proposition
`AffineAdjointWeilRestrictionStatement`. It is the affine adjoint specialization of Conrad,
*Reductive group schemes* (2014), Remark 6.4.5, p. 233. That remark gives the adjoint variant of
Proposition 6.4.4, pp. 232–233. Over an affine base `Spec A`, a fibrewise nontrivial semisimple
group with adjoint geometric fibres is isomorphic to `R_{B/A}(G')` for a finite, projective, étale
`A`-algebra `B` with `Spec B → Spec A` surjective and a reductive `G'` over `Spec B` with adjoint,
absolutely simple geometric fibres. The uniqueness clause gives only the existence of a pair: an
`A`-algebra isomorphism `B'' ≃ B` together with an isomorphism from `G'` to the corresponding base
change of `G''`. As the target's Markdown records, the source's uniqueness says more: every
isomorphism of Weil restrictions comes from a unique such pair. This file does not prove that
uniqueness, Proposition 6.4.4 itself (the simply connected case), or the case of a non-affine
base. The route above is internal; the imported construction modules document each implemented
argument.
