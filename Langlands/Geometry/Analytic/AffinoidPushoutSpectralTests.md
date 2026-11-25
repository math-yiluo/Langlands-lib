# Spectral displacement on affinoid pushouts

This module derives a spectral version of the Library's quotient-coordinate
approximation argument. It supplies the analytic function estimates needed on
affinoid patches of a pullback.

`SpectralConvergesOn l φ ψ a` says that for every positive tolerance, eventually
along `l`, every point of the target spectrum gives that bound on the
displacement `φ t a - ψ a`. The maps are bounded homomorphisms of the presented
affinoid algebras over the same field. The definition uses the existing
`BanachSpectrum.SpectralBound`.

A target point pulls back along each bounded map to a source point, so the
source norm uniformly bounds the spectral value of every image. For sums,
the ultrametric inequality combines two displacements at the same tolerance.
For products, expand the difference into two terms and shrink the input
tolerance using the source norms of the factors. Scalar elements have zero
displacement.

`spectralConvergesOn_of_coordinates` forms the subalgebra of sections satisfying
the convergence condition and proves that it contains the finite monomial sums
in the original coordinates. The quotient norm approximation from
`CoordinateContinuity` gives such a sum close to any section. The source norm
bound controls the approximation error under both maps, and the ultrametric
inequality combines these bounds with the displacement of the sum.

`AffinoidPushout.spectralConvergesOn_of_factors` uses the two coordinate blocks
of the pushout presentation. Every coordinate comes from one of the factors.
The spectral bound for the pullbacks of all factor functions therefore
controls the displacement of every function in the pushout algebra.
