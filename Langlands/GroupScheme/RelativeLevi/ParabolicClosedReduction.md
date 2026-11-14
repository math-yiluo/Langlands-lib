# Closedness from an etale-local dynamic description

Author: Worker 589.

This is an internal reduction toward the published
`Langlands.GroupScheme.RelativeParabolicClosedStatement`. It does not prove the target
unconditionally: its final theorem requires the separate
`RelativeParabolicEtaleLocalDynamicStatement`.

The implemented proof has three parts. First, a representative of a dynamic parabolic
is closed by comparison with the closed representative provided by the published
`dynamicBaseRepresentability` over any base scheme. Second, a monic homomorphism is
closed once its base change to an etale cover is closed: each local morphism is finite,
finiteness descends along an fppf cover of the target, and a finite monomorphism is a
closed immersion. The pullback cover of the target is obtained from the supplied
cover of the base, with `baseChange_map_isPullback` identifying the actual
base-changed homomorphisms. Third, the local dynamic hypothesis provides those closed
base changes. Reductivity supplies affineness and local finite presentation of G, and
the relative parabolic hypothesis supplies monicity.

All schemes and quantifiers have the same universe as the original target. No affine,
noetherian or nonempty hypothesis on the base is imposed. The reduction uses only
published theorems in its imports and the explicitly named local-description hypothesis.
Its provenance is derived/internal. Conrad, *Reductive group schemes* (2014),
Proposition 5.2.3, pp.152–153, motivates the local description; the formal descent route
uses finiteness and monicity.
