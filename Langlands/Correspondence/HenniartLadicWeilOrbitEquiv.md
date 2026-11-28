# Unramified-twist orbit comparison for ℓ-adic Galois and complex Weil classes

`ladicWeilOrbitEquiv` takes a continuous irreducible Weil transport
for each irreducible \(\ell\)-adic class. It sends the orbit of a
Galois class to the orbit of its transport. The class comparison
preserves and reflects unramified twists, giving a well-defined
injective map on the orbit quotients. Every complex Weil class has an
unramified twist arising by transport, so the orbit map is surjective.
[Twist comparison](HenniartLadicWeilClassTwist.md) ·
[Finite-image models](HenniartLadicFiniteImageModel.md)

The parameter map gives a bijection between the stabilizing characters
of matched classes, hence their torsion numbers agree. The definition
of the \(\ell\)-adic Swan witness uses the transported Weil class.
Preservation of rank, Swan witnesses and torsion numbers under
unramified twisting then gives equality of the images of the refined
strata with their Weil counterparts.

`ladicWeilOrbitComparison_of_transport` applies this construction to
`LadicWeilTransportStatement` and obtains
`LadicWeilOrbitComparisonStatement` at the same universes.

The orbit construction develops the coefficient comparison in
`henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§§4.1–4.2, printed pp. 509–510 (PDF pp. 14–15).
