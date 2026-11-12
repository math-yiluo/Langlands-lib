# A special vertex in a prescribed compatible standard-Levi apartment

This internal construction combines the published standard-cocharacter,
Levi projection, special-point and full omega-compatible uniqueness results.
For an ambient connected reductive group with a maximal split torus, a full
omega-compatible apartment class whose ordinary affine roots cover every
actual relative-root direction, a generic cocharacter and a subset of its
simple roots, it constructs a special vertex in any supplied full
omega-compatible standard-Levi apartment class. The resulting vertex
literally restricts the valuation of the original ambient special point on
every Levi root and rational Levi point.

The published standard-cocharacter proof realizes the actual standard Levi
as a dynamic centralizer. The published Levi projection constructs a
restricted apartment class and surjectively projects the ambient apartment
onto it. Literal valuation restriction transfers full omega compatibility
to that class. The centralizer comparison in `LeviApartmentComparison`
transfers the prescribed class's full omega compatibility to the same
centralizer representative. The published uniqueness theorem then
identifies these two apartment classes. The construction returns the
published projected special vertex, whose vertexhood uses the ambient
root-direction coverage; no ambient vertex hypothesis is needed.

This is a derived adapter. It proves neither the existence of available
building data nor compact-subgroup equality. It takes the supplied full
omega-compatible Levi class as data and does not assume either the global
apartment-restriction statement or the global special-point-restriction
statement as a proposition input.

The local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
