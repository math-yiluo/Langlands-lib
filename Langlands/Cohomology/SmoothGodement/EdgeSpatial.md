# Proper spatial maps of the full coefficient invariants edge

This internal construction uses the existing smooth Godement compact complex,
its termwise whole-group invariants, and the full locally constant smooth
coefficient sheaf functor. The commutative ring, topological group, acted-on
spaces and coefficient carriers share universe `u`. Each action is continuous
in the space variable and has stable neighbourhoods. A spatial map is an
actual continuous equivariant map with an explicit properness proof.

`coefficientInvariantsEdge` is the existing `godementEdge` for
`smoothInvariants`, evaluated on every original smooth coefficient object
and intertwiner. Its source takes invariants before module homology; its
target takes invariants of smooth-representation homology.
`coefficientInvariantsEdgeArrow` retains this natural transformation as an
object of the arrow category of full coefficient functors.
The edge is invertible in degree zero. Invertibility in every degree retains
the explicit hypothesis that invariants preserve homology.

`coefficientInvariantsEdge_pullback` proves the all-degree commuting spatial
square. Evaluate at a coefficient object, identify the existing invariant
chain pullback with termwise invariants of the existing compact chain
pullback, and apply naturality of `LeftExactHomology.homologyNatTrans` to
that actual chain map. No exactness of invariants is used in this square.

`coefficientInvariantsEdgePullback` packages the square as an actual arrow
morphism. Its left side is the previously constructed invariant cohomology
pullback. Its right side is the invariants of the previously constructed
smooth compact cohomology pullback. The two projection formulas are
definitional. Identity and strict contravariant composition follow by arrow
extensionality and the existing laws for these two maps.

The provenance is internal specialization of the published left-exact
homology comparison and actual proper full coefficient spatial chain maps.
This concerns ordinary-open smooth coefficient sheaves. It supplies no
sheaf-derived spatial pullback or comparison isomorphism in higher degrees,
Godement resolution exactness or acyclicity, analytic etale realization,
uniformization, Shimura specialization or Harris compatibility.
