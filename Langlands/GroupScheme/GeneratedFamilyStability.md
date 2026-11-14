# Stability and centralizers of generated families

This internal derived module uses `IsGeneratedByFamily` and the closed
representability of an orbit core and of a subgroup centralizer. It adds no
literature input.

For an arbitrary field and a family indexed in an independent universe, every
generating range lies in the generated range. Minimality can consequently be
applied using containment of ranges on all test schemes in place of a source
factorization.

If an affine group acts on the ambient group and preserves every generating
range, the generated range is stable. The orbit core of the generated range
has a closed representative. Stability of the generators puts each generating
range in this core, so minimality puts the generated range in the core.
Evaluating its defining orbit condition on the identity refinement proves
stability. Smoothness and connectedness are unnecessary.

`IsGeneratedByFamily.action` constructs the resulting automorphic action on
the closed generated subgroup by the published represented-subgroup action
construction. `action_act_comp` states that its inclusion intertwines this
action with the ambient one on every test scheme.

When the ambient group is affine, a closed subgroup that commutes with every
generator commutes with the generated range. Its full centralizer has a
closed representative over the field, so this is another application of
minimality. The centralizer is not assumed smooth or reduced. All statements
use arbitrary scheme tests and their refinements.
