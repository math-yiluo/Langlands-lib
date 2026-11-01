import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain

/-! # Cancellation for full affinoid-domain representations -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The full bounded factorization property cancels a representing structural
map on algebra homomorphisms to any presented affinoid test algebra. -/
theorem Represents.hom_ext {A B : PresentedAffinoidAlgebra K}
    {i : BoundedAlgHom K A B} {U : Set (BanachSpectrum A)}
    (hi : Represents K i U) (R : PresentedAffinoidAlgebra K)
    (ψ χ : BoundedAlgHom K B R) (heq : ψ.comp i = χ.comp i) : ψ = χ := by
  have hφ : HasImageIn K (ψ.comp i) U := by
    intro x
    change BanachSpectrum.comap i.toBoundedRingHom
      (BanachSpectrum.comap ψ.toBoundedRingHom x) ∈ U
    exact hi.hasImageIn _
  exact (hi.2.2 R _ hφ).unique rfl heq.symm


end Langlands.Analytic.PresentedAffinoidAlgebra
