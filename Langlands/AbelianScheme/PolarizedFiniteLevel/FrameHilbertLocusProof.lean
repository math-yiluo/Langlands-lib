import Langlands.AbelianScheme.PointedProjectiveAbelianLocusProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocusProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertLocusReduction

/-! # The frame-normalized Hilbert locus -/

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- An immersion of the base carries a frame-normalized realization of the
projective family and classifies all such realizations by factorization. -/
theorem frameHilbertLocus : FrameHilbertLocusStatement :=
  frameHilbertLocus_of_pointedAbelian_and_cubicPolarization
    Langlands.AbelianScheme.pointedProjectiveAbelianLocus.{0} cubicPolarizationLocus.{0}

end Langlands.AbelianScheme.PolarizedFiniteLevel
