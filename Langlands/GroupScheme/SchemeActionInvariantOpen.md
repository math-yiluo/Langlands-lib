# A scheme action on an invariant open subscheme

This internal construction works over any base scheme `S : Scheme.{u}`.
Given an actual `SchemeAction H X` and an open `V` of `X.left`, it defines
`IsInvariantOpen V` as equality of the inverse-image opens under the action
morphism and the second projection on the actual product scheme.

`openSubscheme V` is the open subscheme with its inherited structure map
over `S`; `openSubschemeι V` is its open immersion into `X`. `liftToOpen`
factors any relative morphism whose whole scheme image lies in `V` through
this open subscheme. The factorization identity is `liftToOpen_comp`.
These constructions use Mathlib's actual open subschemes and the universal
property of an open immersion.

For an invariant open, `IsInvariantOpen.mem_act_iff` proves that, for any
scheme test `Z`, any group point `h`, any point `x` of `X` and every
underlying scheme point of `Z`, membership in `V` is equivalent before and
after the action. `range_act_subset_iff` applies this to the whole image of
the test morphism. These statements concern actual scheme points, with no
topology assigned to a set of rational points.

`invariantOpenActionHom` factors the action on the product with the open
subscheme through the open itself. `onInvariantOpen` equips that morphism
with the categorical action structure. Its identity and multiplication
laws follow by composing with the open immersion, using the ambient action
laws, and cancelling the monomorphism. `onInvariantOpen_act_comp` proves
equivariance of the inclusion on every scheme test.
`isFixed_onInvariantOpen_iff` proves that this inclusion preserves and
reflects all-test fixed points, by equivariance and cancellation. Finally,
`isFixed_liftToOpen` transfers any ambient all-test fixed point whose image
lies in `V` to an all-test fixed point of the induced action.

The provenance is internal: these are open-immersion factorization and
categorical-action constructions for using invariant affine charts in the
flag-step argument. They establish neither the existence of invariant
affine opens nor the closedness of unipotent orbits. The invariant-open
condition is definitionally the action/projection equality requested by
`FlagInvariantAffineOpenCoverStatement`.
