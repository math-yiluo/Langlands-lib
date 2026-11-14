# Perfect-field lifting through actual smooth root maps

Internal extension of `SmoothRootQuotient`, retaining the actual intrinsic
character root functors and the exact restricted root homomorphism.

The key extra point is that the full kernel of the restricted smooth root map
is connected. This is not inferred from connectedness or unipotence of the
ambient kernel. The source root representative has an actual split-torus
action supported in strictly positive multiples of its defining character.
A cocharacter pairing positively with that character contracts the entire
source root group. The restricted root homomorphism intertwines the torus
actions, so its full scheme-theoretic kernel is stable under this contraction.
The closed subgroup functoriality of identity limits contracts the kernel
itself. Connectedness follows from the published contraction theorem, and
unipotence follows by realizing the same contracted group as a dynamic
unipotent subgroup in its semidirect product with `Gm`.

The source and target groups are smooth and affine over an arbitrary field,
the acting torus is split, the character is nonzero, and the original
homomorphism is smooth. The proof does not require connectedness of the ambient
groups, maximality of the torus, or occurrence of the character as an actual
root. All constructions have arbitrary universe `u`.

Over a perfect field, the smooth full kernel of the root map is split unipotent
by `perfectFieldUnipotentSplit`. The already proved smooth surjectivity of the
root map makes it an actual fppf quotient by that full kernel. The published
split-unipotent torsor theorem gives a rational source point above every
specified target point. Composing the two root inclusions retains the exact
image under the original homomorphism.

`perfectFieldRootPointLift` chooses an actual source point from a prescribed
target point in the intrinsic root subgroup, with both source root membership
and exact original image in its subtype. It uses perfection, with no algebraic
closedness or ambient unipotent-kernel premise. These are internal consequences
of the contraction, root tangent support, smooth root-map and torsor theorems
named in the imports. The unit does not assert integral lifting or the final
facet root datum.
