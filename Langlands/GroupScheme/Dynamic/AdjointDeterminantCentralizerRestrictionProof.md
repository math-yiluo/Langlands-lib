# Levi restriction of the parabolic adjoint determinant

The theorem
`Langlands.GroupScheme.Dynamic.adjointDeterminantCentralizerRestriction`
has exactly the published proposition
`Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionStatement.{u}`
as its entire type. The statement is imported by module name. Its pair and all
its dependencies are unchanged.

The proof first establishes
`Dynamic.parabolicAdjointAction_restrict_centralizer` over an arbitrary base
scheme. The uniqueness theorem `eq_centralizerAdjointAction` reduces equality
of the actions to their formulas after the represented unipotent inclusion,
on every scheme test. The restriction formula `AutomorphicAction.restrict_act`
and `parabolicAdjointAction_act_comp` give conjugation by the image of a
centralizer point in the parabolic. Applying `congrArg` to
`centralizerToParabolic_comp` identifies this image in the ambient group with
the centralizer inclusion. Both actions therefore give `m*u*m⁻¹`.

The proof then uses the published lemma
`AutomorphicAction.determinantCharacter_restrict`, imported from
`Langlands.GroupScheme.Dynamic.AdjointDeterminantFunctorialityProof`.
It says that restricting an action's determinant character along an actual
homomorphism gives the determinant character of the restricted action,
using the same natural finite coordinates on the same actual Lie module.
That published lemma follows from compatibility of the finite representation
with restriction and composition of characters. It is used as a proved
Library theorem, with no additional mathematical premise.

The final theorem introduces exactly the original statement's hypotheses,
exposes `adjointDeterminantCharacter` as the determinant character of the
parabolic action, applies the published determinant restriction lemma and
rewrites by the established equality of actions.

This is an internal derivation from the published automorphic actions,
representing inclusions and determinant-character constructions. It applies
over every commutative base ring and in every characteristic; trivial
cocharacters and zero-dimensional finite coordinates are allowed. It requires
no separatedness of the ambient group. Finite coordinates remain the
statement's input; the proof does not assert their existence. Absolute
values, Haar measures and analytic modulus functions play no part in it.
