# Connectedness of the centralizer intersection with a Borel

Author: Worker 1479.

This internal adapter derives connectedness from the published
`dynamicConnected` proof and applies the published structural Borel equivalence.
It uses the actual pullback intersection and its projections throughout.

For an affine group scheme over an arbitrary field, a Borel subgroup containing
the full range of any cocharacter, and any closed representative of the ambient
dynamic centralizer, `IsBorelSubgroup.connectedSpace_centralizer_intersection`
constructs a `ConnectedSpace` witness for the actual pullback intersection.
The proof restricts the cocharacter to the
Borel, uses the published all-test representative identity for the second
projection, and applies the centralizer branch of `dynamicConnected`. Its
premises hold because a Borel is smooth and connected, and it is
affine as a closed subgroup of the affine ambient group.

`IsBorelSubgroup.centralizer_intersection_isBorel_iff` then applies the structural
module's Borel equivalence with that connectedness proof. Thus the actual
first projection is Borel if and only
if the prescribed ambient Borel contains some Borel of the chosen centralizer.
The reduction imposes no smoothness or connectedness premise on the ambient
centralizer and works over any field.

Finally, `IsBorelSubgroup.centralizer_intersection_isBorel_of_statement` applies
that equivalence to an explicit instance of
`CentralizerBorelIntersectionStatement` under all of its original hypotheses.
It is an upgrade for consumers of the existence statement and does not prove
that statement. All ranges and representatives retain every test scheme; the
cocharacter may be trivial or noninjective. These are derived logical and
geometric adapters to the published interfaces, with no new external source
claim.
