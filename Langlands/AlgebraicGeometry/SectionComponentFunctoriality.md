# Functoriality of fibre components selected by sections

This internal construction starts with a commuting square of scheme morphisms
`g : X' → X`, `b : Y' → Y`, `f' : X' → Y'` and `f : X → Y`, with actual
sections `e'` and `e` satisfying `e' ≫ g = b ≫ e`. It assumes no smoothness,
finiteness, separation or openness property.

For each point `y'` of `Y'`, `fiberMap` is the actual morphism
`X'_{y'} → X_{b(y')}`. It is the pullback map induced by `g`, `b` and
the canonical map `Spec κ(y') → Spec κ(b(y'))`. Its first projection
commutes with the fibre inclusions. Since these inclusions are topological
embeddings, that projection identity and compatibility of the sections
show that the selected fibre point maps to the selected fibre point.
Continuity then sends its entire connected component into the connected
component of its image. The union over all `y'` yields
`g(componentSet f' e') ⊆ componentSet f e`.

The proof uses Mathlib's pullback map, naturality of the canonical
residue-field-valued maps, and preservation of connected components by
continuous maps. It supplies only this functoriality and does not assert
an equality, openness or base-change invariance of the component union.
