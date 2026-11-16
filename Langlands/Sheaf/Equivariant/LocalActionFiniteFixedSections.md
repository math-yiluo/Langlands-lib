# Simultaneous fixed sections for finite local-action families

This is an internal construction from `LocalAction.IsDiscreteSection` and
`LocalActionSystem.IsDiscrete`. It concerns presheaves on any category with a
local action system for a group with a topology. It requires neither a
Grothendieck topology nor continuity of multiplication. The finite-intersection
argument is the same one used by the published finite-limit discreteness
construction; here its inputs may be sections over different objects.

`CommonFixedSections F U H a s Q` stores an open subgroup contained in the
prescribed open subgroup `Q` and each acting subgroup `H i`. Its `fixes` field
states that this subgroup fixes every supplied section `s i` under the action
`a i` on `U i`. The index type need not be finite to define this data.

For a finite index type, `nonempty_commonFixedSections` assumes discreteness of
each supplied section. Choose its open fixing subgroup `N i`, then intersect
the finitely many `N i` with `Q`. Each chosen subgroup is contained in its
acting subgroup, so their intersection has all required inclusions and
fixedness properties. For an empty family the intersection is the whole group
and the resulting subgroup is `Q`. `LocalActionSystem.commonFixedSections`
chooses these data when the presheaf is discrete and all supplied actions are
admissible. Multiple sections over one object can be included by repeating
that object and action in the finite family.

`fixed_restrict_of_intertwines` states fixedness after restricting along an
arrow which strictly intertwines its two actions on the given common open
subgroup. The proof uses the presheaf composition law, the intertwining equality,
and the fixedness of the original section. The subgroup stays the same; local
equivariance without the supplied intertwining equality is not a hypothesis of
this result.

For coefficients in a module category over a commutative ring,
`fixedFamilySubmodule F a N` is a submodule of the product of the section modules.
Its membership condition tests each action on elements of `N` which belong to
that action's subgroup. In particular, when `N` is contained in every acting
subgroup, this is exactly the simultaneous fixed-family submodule.
Linearity of the presheaf maps proves closure under zero, addition and scalar
multiplication.

`CommonOpenSubgroup Q H` restricts the indexing subgroups to those contained in
`Q` and every `H i`. Shrinking a subgroup enlarges its fixed-family submodule,
and intersecting two indexing subgroups proves that these submodules are a
directed family. For a finite family of discrete sections,
`exists_mem_fixedFamilySubmodule` proves membership in one such submodule.
Consequently, `LocalActionSystem.iSup_fixedFamilySubmodule` proves that their
supremum is the whole product when the presheaf is discrete and every action is
admissible. This is an exhaustion by a directed family of submodules, not a
construction of a categorical colimit.

These results only concern supplied finite families of objects, actions and
sections. They construct no compact basis, fiber products, Čech nerve or
hypercover, and they do not establish injective acyclicity or a derived
comparison theorem.
