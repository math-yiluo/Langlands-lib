# Subgroup restriction and actual smooth subquotients

This internal construction packages the existing subgroup restriction as a
functor and derives its elementary subquotient laws. It works for any group
with a topology, any subgroup with its induced topology, and smooth complex
representations. The group universe `uG` and carrier universe `uV` are
independent. No normality, openness, admissibility, irreducibility, or
semisimplicity hypothesis is needed.

`Langlands.SmoothRep.restrictSubgroupFunctor N` uses the published
`restrictSubgroup` on objects and `restrictSubgroupMap` on intertwiners. The
carrier and linear maps are unchanged; identities and compositions are
preserved definitionally. Smoothness is supplied by the existing restriction
construction using continuity of the subgroup inclusion.

`IsSubquotient.restrictSubgroup` starts with the published characterization
`isSubquotient_iff_exists`: an object `C` injects into the ambient object `A`
and surjects onto `D`. Restricting these two maps preserves their underlying
functions, so the same injectivity and surjectivity proofs supply an actual
subquotient presentation after restriction. Thus the conclusion concerns the
published relation built from invariant submodules, their quotients, and an
actual smooth-category isomorphism.

`restricted_subrepresentation_isSubquotient` applies the published
`smoothSubquotientTransitivity` to the inclusion of `W` in the restriction of
`D` and the restricted subquotient presentation. The imported transitivity
proof takes the inverse image of an invariant submodule under the surjection,
then uses its inclusion and the induced surjection onto the desired quotient.
This supplies the preimage step without duplicating it here.

`not_isSubquotient_of_restricted_subrepresentation` is the contrapositive:
if one actual subrepresentation of restricted `D` is excluded as an actual
subquotient of restricted `A`, then `D` cannot be an actual subquotient of `A`.
It does not assert that such an excluded subrepresentation exists.

These are internal algebraic consequences of the existing actual restriction,
subquotient presentation, and transitivity constructions. They provide the
subquotient-exclusion step needed in cuspidal block isolation. They do not
prove compact-coefficient splitting, produce a finite restriction family, or
prove the block-isolation theorem.
