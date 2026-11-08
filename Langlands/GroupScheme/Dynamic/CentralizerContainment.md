# Tangent containment for cocharacter centralizers

Worker 146. This is an internal derived helper for the absolute Borel-overgroup cocharacter proof. It introduces no external mathematical premise.

`Dynamic.centralizer_le_range_of_tangentSubmodule_le` works over an arbitrary field. Let `G` be smooth, connected and affine, let `i : P ⟶ G` be a closed subgroup with `P` smooth and connected, and let `χ` be a cocharacter of `P`. If the actual tangent submodule of the ambient cocharacter centralizer `Z_G(χ ≫ i)` lies in the actual tangent submodule of `range i`, then `Z_G(χ ≫ i) ≤ range i` as subgroup functors on every test scheme.

The proof represents the ambient centralizer by `M` and its intersection with `P` by `Q`. The intersection represents the internal centralizer `Z_P(χ)` by `Dynamic.isRepresentedBy_intersectionSnd`. Published dynamic centralizer smoothness and connectedness therefore apply to both `M` and `Q`. The tangent submodule of the intersection is the intersection of the tangent submodules, so the assumed inclusion makes it equal to that of `M`. The published `RelativeRoot.IsSmoothConnectedClosed.eq_of_le_of_hasLieImage` identifies these two smooth connected closed subgroup functors. The intersection is contained in `P`, giving the conclusion.

The separate smoothness of this particular intersection is essential to the implemented argument. The lemma makes no assertion identifying arbitrary closed subgroups from Lie algebra equality.
