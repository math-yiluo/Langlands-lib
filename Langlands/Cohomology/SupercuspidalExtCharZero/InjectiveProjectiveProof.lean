import Langlands.Cohomology.SupercuspidalExtCharZero.Admissibility
import Langlands.Cohomology.SupercuspidalExtCharZero.Injectivity
import Langlands.Cohomology.SupercuspidalExtCharZero.Projectivity

/-!
# Irreducible representations with compact coefficients are injective and projective

Over a field of characteristic zero, an irreducible smooth representation with compactly
supported matrix coefficients is projective, has finite-dimensional fixed vectors under
compact open subgroups, and is therefore injective.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Cohomology.SupercuspidalExtCharZero

universe u

/-- Over a field of characteristic zero, an irreducible smooth representation with
compactly supported matrix coefficients is an injective and a projective object of the
category of smooth representations. -/
theorem compactCoefficientInjectiveProjective
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] :
    CompactCoefficientInjectiveProjectiveStatement k G μ := fun ρ hirr hc =>
  ⟨injective_of_hasCompactCoefficients ρ hirr hc fun K hK =>
      finiteDimensional_fixedVectors ρ hirr hc K hK,
    projective_of_hasCompactCoefficients ρ hirr hc⟩

end Langlands.Cohomology.SupercuspidalExtCharZero
