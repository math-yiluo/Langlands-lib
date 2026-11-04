# Functoriality of actual adelic-level model point topologies

`Langlands.Global.AdelicLevelModelFunctorialityStatement` states that actual
postcomposition by a morphism X → Y of models over the same S-integer ring is
continuous on the actual adelic-level-valued points. It has one curve-place
clause and one full number-field clause, at an arbitrary common universe.
The source and target topologies are explicitly the published
`curvePlaceLevelModelPointTopology` or `numberFieldLevelModelPointTopology`.
They are induced along the original arithmetic coordinate maps into products
of independent local scheme-point topologies.

X and Y are arbitrary schemes over the indicated original S-integer base.
There is no affine, finite-type, quasi-compact, quasi-separated or separated
hypothesis. All finite S, including empty S, are included. The curve clause
requires arbitrary fields k and F and an algebra action k → F, with no
function-field finiteness, finite-constant, perfectness or separability premise.
The number-field clause requires `NumberField K` and retains all infinite
completion factors.

This is a derived functoriality consequence of the local scheme-point
topologies, the actual coefficient projections and the actual pullback
comparison on points. At each local factor, postcomposition by the base-changed
model morphism is continuous because the local ring has continuous
multiplication and `IsOpenUnits`. Naturality of the actual point base-change
equivalence then identifies its composite with the corresponding arithmetic
coordinate of postcomposition. Products and the explicitly induced topology
give the stated continuity. These are mathematical proof ingredients; the
present file is only the exact statement target.

The result provides functoriality within a fixed level in the construction of
Conrad's Theorem 3.6 (printed pp.6–8). It is not a quotation of a separate source
assertion. Changing S also changes the scalar ring and the model, so transition
maps require additional coefficient and base-change comparisons. Their
openness and injectivity qualifications, model descent, independence and the
global adelic-colimit topology remain separate parent obligations.
