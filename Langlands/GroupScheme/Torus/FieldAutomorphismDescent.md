# Descent of automorphisms of a supplied split torus

This internal construction descends every automorphism of the pullback of an actual split commutative torus over a field. The base map may be any scheme morphism between the spectra of two fields in the same universe; no separability hypothesis is used. The equality concerns the supplied actual torus automorphism, not merely its character action or rational points.

The coordinate helper `splitTorus.fieldCommAutomorphismExtension` is the published `splitTorus.fieldAutomorphismExtension` in commutative notation. Its base-change equation is the published equation for that construction. The integral character coordinates of a field split-torus automorphism extend over every base scheme, and specialize to the original map.

For the arbitrary supplied torus, `IsSplitTorus.automorphism_baseChange_surjective` chooses a splitting isomorphism over the ground field. Its base change followed by the canonical coordinate-torus identification gives a splitting isomorphism over the second field. Conjugating the supplied automorphism by this isomorphism gives a coordinate automorphism. Extend its integral coordinates over the ground field, then conjugate back by the original splitting isomorphism. The coordinate base-change equation and cancellation of the splitting isomorphisms show that base change of the resulting automorphism equals the exact supplied automorphism.

`IsSplitTorus.descendedAutomorphism` chooses such a descent, and `IsSplitTorus.descendedAutomorphism_spec` records its equality after base change. This supplies the automorphism step for normalizer rationality. It does not assert descent of a supplied normalizing point.
