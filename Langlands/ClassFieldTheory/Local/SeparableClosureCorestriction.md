# Corestriction on actual separable-closure unit cohomology

For a finite separable extension \(L/K\), the chosen separable
closure of \(L\) is separably closed and separable over \(K\).
The chosen \(K\)-embedding of the lower separable closure into
it is therefore an isomorphism. Pull the copy of \(L\) back through
this isomorphism. Its fixing subgroup in the lower closure is open.

`separableUnitCorestriction` transports the upper continuous unit
cohomology through the field isomorphisms, then applies the actual
continuous transfer from this open subgroup. The reverse coefficient
transport follows restriction in `separableUnitRestrictionBySubgroup`.
The two transports cancel in the composite. The continuous transfer
index formula and the linear equivalence with the embedded copy of
\(L\) show that this composite is multiplication by \([L:K]\).

This implements the common-closure description of continuous
corestriction in Serre, *Local Fields* (1979), Chapter XI, §§1–2,
pp. 166–168. All coefficient maps act on actual field units and
the construction uses separable closures in every characteristic.
