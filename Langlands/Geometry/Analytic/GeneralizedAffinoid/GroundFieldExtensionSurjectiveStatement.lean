import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension

/-! # Surjectivity of the spectrum projection of a ground field extension -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

/-- For complete ultrametric fields `K` and `L` with `NormedAlgebra K L`, and
every presented `K`-affinoid algebra `A`, every point of the Berkovich
spectrum of `A` is the restriction along `ι : A → A_L` of a point of the
spectrum of the ground field extension `A_L`. -/
def SpectrumProjectionSurjectiveStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] (A : PresentedAffinoidAlgebra K),
    Function.Surjective (spectrumProjection K L A)

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
