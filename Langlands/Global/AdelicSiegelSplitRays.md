# Fundamental split rays in the positive Siegel torus

The fundamental coweight points in the intrinsic positive maximal split torus have
zero ambient character logarithm. A positive point factors through the derived
split factor and the connected split centre in the Siegel setup. The derived factor
has zero ambient character logarithm, so the split-centre factor is also norm one.
The positive split-centre decomposition makes that factor the identity.

`exists_siegelFundamentalRays` puts each fundamental point in the Siegel torus.
Its own simple-root logarithm is positive and all other simple-root logarithms are
zero, so every nonnegative integral power lies in the weak chamber of threshold one.
When a Levi index omits that simple root, all its roots vanish on this point and the
positive split-component criterion identifies the resulting point in the parabolic.

`AdelicSiegelSplitRaysStatement` records these properties for any algebraic Siegel
setup of the given family. The rays realize the simple-root translations in
Bernstein–Lapid, *On the Meromorphic Continuation of Eisenstein Series* (2024),
§7.2, p. 211, with the split decomposition of §6.1, pp. 199–200.
