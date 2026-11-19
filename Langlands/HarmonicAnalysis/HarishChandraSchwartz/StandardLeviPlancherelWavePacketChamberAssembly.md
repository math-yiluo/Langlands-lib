# Assembly of the original wave-packet chamber estimates

`StandardLeviPacketProperRegionDerivativeEstimates` is the remaining
pointwise estimate on the proper-parabolic regions of the actual closed
minimal-Levi chamber. For each proper standard Levi, each positive
positive-part parameter, and each input level and real order, it asks
for a positive threshold, a finite collection of input derivative
indices and a nonnegative scalar. They bound the original
source-normalized packet at points in both the threshold region and
the positive-part region, relative to the original `rationalXi` and
full `rationalHeight`. The witnesses are uniform over the varying
section at that level.

`standardLeviPacketChamberDerivativeEstimates_of_properRegions` combines
this premise with the proved central Fourier estimate. It uses a compact
ambient subgroup with a simultaneous standard basis and both the
minimal-Levi and inducing-Levi Cartan coverings. The given seminorm of
the minimal-Levi real cocharacter space is positive definite.

The chamber comparison gives one positive-part parameter for the finitely
many proper standard Levis. At each level and order the proof takes a
common upper bound on their thresholds. A chamber point then lies in one
of two regions. If its full matrix height is controlled by the central
coordinates, the proof applies the original packet's central estimate
at order `max r 0` and rescales its finite seminorm bound. Otherwise the
point meets both region conditions for a proper standard Levi. The
corresponding proper-region estimate applies because its threshold is
at most the common bound. The union of all the selected input indices
and the sum of their nonnegative multipliers work on the full chamber.

The conclusion is `StandardLeviPacketChamberDerivativeEstimates` for the
same inducing representation, weight, measures, section topology and
matrix representation. The Cartan transfer and synthesis theorems use
this conclusion. The proper-region estimates themselves require the
remaining weak and positive constant-term arguments of Waldspurger's
VI.3.1 proof, printed pp. 303–305.
[Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)
