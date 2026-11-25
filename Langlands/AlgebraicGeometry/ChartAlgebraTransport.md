# Compatible point transport from chart algebra transitions

This internal construction takes a functorial family of chart-transition
isomorphisms between the actual tensor algebras `T tensor_B C` for specified
chart maps `B → T`. It retains the identity, cocycle and coefficient-naturality
laws. Tensor adjunction turns these into transport of compatible algebra
points `C → T` between chart maps. The module proves identity, composition and
naturality of this transport.

The transition convention is that the algebra isomorphism indexed by
`(f1, f2)` goes from the `f2` tensor algebra to the `f1` tensor algebra. Point
transport is contravariant: extend the old point from the `f2` tensor algebra,
precompose the inverse-direction transition, and use tensor adjunction to
obtain a point over `f1`. Every tensor algebra uses the actual scalar action of
its displayed chart map. No flatness, étaleness, finiteness or nonzero-ring
hypothesis is needed.

The construction is an internal preparation for converting the functorial
algebra data in finite étale chart descent into the existing faithfully flat
algebra coaction. It does not construct the descended algebra or assert
effectivity of the chart datum; `ChartAlgebraDescent` does.
