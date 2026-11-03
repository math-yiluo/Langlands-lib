# Full coefficient Godement diagrams on proper induced rational transport

This internal construction assembles the existing proper spatial maps on
actual induced rational spectra into contravariant diagrams. The indexing
category is `SmoothProperTransport`: its objects retain an open subgroup,
an invariant rational domain and the balanced quotient spectrum, with stable
neighbourhoods for its full group action; its arrows retain the original
rational transport arrow and require its actual induced continuous map to
be proper. The complete ultrametric normed field, presented strict affinoid
algebra, topological group, commutative coefficient ring and smooth coefficient
carriers share universe `u` in this module.

Each diagram takes values in a category of functors on the full original
`SmoothRep R G`. Thus every object and every intertwiner of that coefficient
category remains present, in addition to naturality in spatial transport.
`compactFunctionsDiagram` uses the original full compact-function
representations and their proper precomposition maps. Its invariant version
postcomposes with the existing whole-group `smoothInvariants` functor.

`godementCompactDiagram` and `godementInvariantCompactDiagram` use the
existing compact smooth Godement complexes and the independently constructed
proper coefficient/spatial chain maps. Their identity and contravariant
composition laws follow from the existing strict laws of those maps.
`godementInvariantCompactDiagramIso` makes the existing identification with
degreewise invariants natural over this spatial category as well as over
coefficients: its naturality is exactly the previously proved chain-map
comparison square.

`godementCohomologyDiagram` applies smooth-representation homology to the
compact complex diagram in each natural-number degree.
`godementInvariantCohomologyDiagram` instead applies module homology after
termwise whole-group invariants. `godementInvariantsEdgeDiagram` is the
original canonical map between these routes as a natural transformation of
spatial diagrams. Its naturality uses the existing spatial edge square;
it assumes no exactness of invariants. It is invertible in degree zero
within the stated hypotheses. Invertibility in every degree has the explicit
additional premise that `smoothInvariants` preserves homology.
`godementInvariantsArrowDiagram` retains the same existing edge and both
components of every existing square as an actual diagram in the arrow
category, using their proved identity and composition laws.

The two sheaf-derived diagrams are restricted to degree zero. Their objects
are the existing actual right-derived compact-section and invariant
compact-section functors evaluated on the full ordinary-open coefficient
sheaves. Their maps are the previously constructed degree-zero pullbacks
transported through the canonical identifications with compact functions.
They do not supply higher derived spatial maps.

The four `ZeroDiagramIso` constructions identify the compact and invariant
Godement cohomology diagrams in degree zero, and their two sheaf-derived
counterparts, with the original compact-function diagrams. For the Godement
diagrams their naturality uses the proved degree-zero compatibility of the
independently constructed all-degree chain maps. For the sheaf-derived
diagrams it uses the existing transported-map squares. Composing these
isomorphisms gives `godementDerivedZeroDiagramIso` and its invariant analogue.
Their component formulas recover the original objectwise comparisons, and
the final natural-transformation equalities prove that both preserve the
canonical compact-function identifications.

The provenance is internal categorical assembly of the published rational
spectrum, proper chain-map, edge and degree-zero constructions. No
cohomology objects, maps or comparison squares are supplied as arbitrary new
data. The coefficient sheaves use ordinary opens of the actual induced
spectra. This does not prove Godement acyclicity, resolution exactness,
unrestricted properness or stable neighbourhoods, higher sheaf-derived
transport, analytic etale realization, uniformization, Shimura specialization
or Harris compatibility. Those remain further obligations of the broader
framework.
