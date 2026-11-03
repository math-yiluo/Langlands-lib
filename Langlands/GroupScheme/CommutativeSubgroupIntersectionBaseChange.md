# Base change and maximality descent for commutative intersections

This internal unit identifies the base change of
`commutativeSubgroupIntersection f r` with the commutative intersection of
the two base-changed maps. The second input map must be a monomorphism
on underlying schemes over the base, as in the intersection construction.
Base change preserves this monomorphism.

`commutativeSubgroupIntersectionBaseChangeIso` is the actual commutative
group-scheme isomorphism induced by the published pullback comparison
`subgroupIntersectionBaseChangeIso`. Its two projection identities identify
the base change of each original intersection map with the corresponding
map of the new intersection.

Over fields, torus structure of the intersection descends from any
extension field: transport it along the pullback comparison and apply
`IsTorus.of_baseChange`. If the first input map is closed, maximal-torus
structure of the intersection's second projection also descends. The proof
first transports the given maximality along the source comparison
isomorphism, uses its second-projection identity to identify the map, then
applies `IsMaximalTorus.of_baseChange`. Closedness of that original
projection follows by pulling back the closed first input map.

These are derived consequences of the existing intersection universal
property, `Langlands.GroupScheme.Torus.MaximalTransport`, and
`Langlands.GroupScheme.Torus.MaximalBaseChangeReflection`. They reduce
the maximal-torus geometry of a radical intersection to its proof over an
extension field, for example an algebraic closure. They do not prove that
geometry over the extension, existence or descent of a solvable radical,
or any Levi existence or multiplication theorem.
