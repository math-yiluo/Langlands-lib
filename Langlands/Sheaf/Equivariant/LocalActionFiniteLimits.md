# Finite limits of discrete sheaves

This internal consequence of local-action discreteness needs no finite
equivariant refinement assumption. For a finite diagram of discrete module
sheaves, each projection of a limit section has an open fixing subgroup.
Intersect these finitely many subgroups with the tested acting subgroup.
Naturality and the joint injectivity of limit projections show that the
intersection fixes the original section.

The resulting closure under finite limits gives finite limits in the full
subcategory of discrete module sheaves and preservation of those limits by
its inclusion into all sheaves. This supplies the limit-preservation input
needed for induction from an open subgroup without adding refinement
hypotheses on that subgroup.

The construction `discreteSheafLimit` takes a finite diagram of discrete
module sheaves and returns the ambient sheaf limit equipped with the
discreteness property proved above. Its underlying sheaf is exactly the
limit of the diagram followed by the full-subcategory inclusion.
