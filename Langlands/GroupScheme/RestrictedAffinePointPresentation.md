# Original objects under a base algebra and their induced presentations

An original object under an algebra `T` has its own `R`-algebra structure
and a specified map from `T`. This map defines its actual `T`-algebra
structure. Restricting that structure back to `R` gives an induced
presentation. The specified map is `R`-linear, so the original and induced
`R`-structures agree through identity maps of the underlying ring.

`originalIso` constructs these identity-carrier isomorphisms as actual
isomorphisms under `T`; `originalNatIso` proves their naturality. Combining
them with the actual base-change point comparison gives
`originalPointIso`, and `originalPointsEquiv` is its multiplicative
comparison on every original object under `T`.

The reconstructed endomorphism recovers the specified transformation on
every such original object: its exact formula on the induced presentation,
followed by naturality along the identity-carrier comparison, proves
`endomorphism_originalPoints`.

This internal construction retains the original algebra structures and
their specified maps. It does not assume they are definitionally identical
to the induced structures.
