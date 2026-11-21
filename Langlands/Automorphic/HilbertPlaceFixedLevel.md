# Realizing a place component in a fixed Hilbert level

`HasPlaceFixedSmoothRealization` uses the actual norm closure of the
embedded place component and its restricted bounded action. It records
the original compact and Lie realization and a continuous complex-linear
map from its genuine smooth vectors to the global smooth vectors at the
supplied fixed Hilbert level. On underlying Hilbert vectors the map is
the subspace inclusion.

The proof starts with a compatible Hilbert realization of a nonzero
component. The fixed subspace is closed, so an algebraic embedding whose
image is fixed on the component has a fixed closure. The closure
inclusion intertwines the local action and the global action restricted
along the local group map. The fixed-level Hilbert comparison applies
at a nonzero sample in the component whose ambient image is smooth.

This internal formulation combines the Library's actual closure
realization and the bounded smooth comparison under a commuting split.
