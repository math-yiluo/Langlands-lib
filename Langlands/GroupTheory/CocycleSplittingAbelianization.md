# Splitting coinvariants are the extension abelianization

This internal comparison identifies the actual coinvariants of the concrete
cocycle splitting representation with the additive abelianization of its
cocycle extension, over the lifted integers and at the full carrier universe.

The forward map is the coordinate map constructed in
`CocycleSplittingCoinvariants`. For the inverse, an extension element with
coordinates `(a,g)` maps to the coinvariant class of `(a,e_g)`, where
`e_g = delta(g⁻¹) - delta(1)`. The action and correction identities for these
augmentation vectors show that this map preserves multiplication, when the
target is written multiplicatively. It therefore factors through the actual
abelianization.

The two maps are inverse on extension elements. To check the other
composition on every coinvariant, the proof writes an augmentation vector
`f` as the sum of its coordinates `f x` times `e_(x⁻¹)`. The extra
identity-coordinate term vanishes because the coordinate sum of `f` is zero.
This proves a scalar-linear equivalence, without an arithmetic assumption.
