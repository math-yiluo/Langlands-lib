# The line-bundle base-change condition is represented by an open scheme

For an actual module sheaf `M` on `Y` and a test scheme `T` over `S`,
`IsLineBundleBaseChange f M T` says that the ordinary module pullback to
`T.left ×_S Y` is locally free of rank one. Suppose `f : Y → S` is universally
closed and locally of finite presentation, `M` is locally finitely presented,
and `M` is flat over `S` through `f`.

`isLineBundleBaseChange_iff` applies the cartesian base-change criterion to
identify this condition with the image of `T → S` lying in the actual open
`rankOneBaseOpen f M`. `lineBundleBaseChangePresheaf` retains a lifted proof
of the actual module condition on each test. It is a subterminal presheaf;
restriction uses the image criterion and the defining equation of a slice
morphism. It is defined on the full slice, with no affine, nonempty,
quasi-compact, or noetherian restrictions.

`lineBundleBaseChangeYonedaEquiv` sends a map into the open scheme to the
pullback line-bundle condition. Its inverse is the actual scheme morphism
`rankOneBaseOpenLift`, with its proved factorization equation. Monicity of
the open immersion proves the inverse identity on scheme maps. Proof
irrelevance proves the inverse identity on condition witnesses and the
naturality of the equivalences. Consequently,
`lineBundleBaseChangePresheafIso` is a natural isomorphism with the lifted
Yoneda presheaf of the open scheme over `S`.

This is an internal construction from `LineBundleBaseOpenBaseChange` and
the actual slice Yoneda interface. It represents a condition on a fixed
module family, and does not itself construct the coherent-family stack
atlas or a point-fibre equivalence for a transformation of pseudofunctors.
The underlying morphism representing this condition is an actual open
immersion. All schemes retain arbitrary universe `u`.
