import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain

/-! # Ground field extension preserves affinoid domains -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

/-- Ground field extension preserves affinoid domains. Let `K` and `L` be
complete ultrametric fields with `NormedAlgebra K L`. If a bounded map
`i : A → B` of presented `K`-affinoid algebras represents the closed subset
`V` of the spectrum of `A` (its spectrum map has image `V`, and it has the
restriction universal property against every presented `K`-affinoid algebra),
then the extended map `i_L : A_L → B_L` represents the preimage of `V` under
the spectrum projection of `A_L`, against every presented `L`-affinoid
algebra. -/
def DomainPreservationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] (A B : PresentedAffinoidAlgebra K) (i : BoundedAlgHom K A B)
    (V : Set (BanachSpectrum A)),
    Represents K i V →
      Represents L (map K L i) (spectrumProjection K L A ⁻¹' V)

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
