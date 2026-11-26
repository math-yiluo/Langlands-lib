# The closed rational locus under analytic ground field extension

Let \(K \to L\) be an isometric extension of complete ultrametric normed
fields, and let \(A\) be an affinoid atlas presentation. The extension
may have arbitrary degree and either field may be trivially valued.
Write \(\pi: A_L \to A\) for the projection of the actual extended
atlas, \(R\) for the \(L\)-rational locus of \(A_L\), and \(S\) for the
\(K\)-rational locus of \(A\). Both rational loci have their induced
topologies.

`GroundFieldRationalLocusStatement` asserts that the inverse image of \(S\)
under the restriction of \(\pi\) to \(R\) is closed in \(R\). It also
asserts that the projection from that inverse image to \(S\) is bijective.
These clauses identify the closed image of scalar extension on analytic
rational points in terms of the projection. They apply to arbitrary
affinoid atlas presentations, with their actual charts and bounded
restrictions.

This is an intermediate assertion in the proof of Proposition 5.11(3),
last paragraph on p. 19, of Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
On the constituent affinoids in that proof the projection restricts
characters to the original algebra. A character descends precisely when
its values there lie in the closed subfield \(K\) of \(L\), and a bounded
character downstairs determines its scalar extension.
