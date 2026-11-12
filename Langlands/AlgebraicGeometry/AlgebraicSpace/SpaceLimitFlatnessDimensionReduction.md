# Reduction to descent of geometrically connected fibres

Author: Worker 156.

`SpaceLimitFlatnessDimensionReductionStatement` is an explicit conditional
statement: descent of the published `HasGeometricallyConnectedFibres`
property implies the unchanged `SpaceLimitFlatnessDimensionDescentStatement`.
Its proof does not establish the premise. In particular, this supporting
unit does not prove the full target unconditionally or complete its task.

The flatness conjunct is supplied by `spaceLimitFlatnessDescends`. For each
natural number `d`, `spaceLimitPureFibreDimensionDescends` gives descent of
pure dimension alone. To combine it with connectedness, first descend pure
dimension to an incoming stage `j`. Naturality of the iterated base-change
isomorphism and the published arrow-isomorphism invariance of geometrically
connected fibres identify the connected-fibre condition at the limit for
the model over `j`.

Apply the assumed connected-fibre descent to that model, retaining the
original cofiltered diagram and limit cone. Quasi-separatedness and the
finite-presentation atlas property are preserved by the first base change,
so all of its hypotheses hold. This gives a further incoming stage `k`
over `j`. Pure dimension is preserved by the second scheme base change.
The natural comparison of iterated and direct base change transports both
properties to the original map over the composite arrow `k ⟶ i`.

The reverse direction applies each of the two descent equivalences to the
same stage witness. Thus both directions produce exactly the required
conjunction at one incoming stage; no uniform-dimension, noetherianity,
representability or additional finiteness hypothesis is introduced.

The included `HasPureFibreDimension.of_arrow_iso` transports the existing
chart witness by composing its source and target chart maps with the
respective presheaf isomorphisms. Étaleness and source surjectivity are
preserved, and the witnessing scheme map, its local finite type and its
actual fibre dimensions stay the same. Naturality of the isomorphism of
arrows proves the new chart commutativity equation.

This is an internal combination of the imported published chart and
base-change constructions and the two supporting descent theorems. The
geometric-connected-fibre descent premise remains an independent obligation.
