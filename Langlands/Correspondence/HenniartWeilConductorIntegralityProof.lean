import Langlands.Correspondence.HenniartWeilConductorIntegralityStatement
import Langlands.LocalFactor.Ramification.ArtinExponent
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof

/-!
# Integrality of the conductors of every presentation of a local Weil representation: proof

The Artin and Swan expressions of a finite inertia presentation `P` of a Weil representation
are those of the descended representation of the inertia group of the finite Galois subextension
`P.extension` over `F` (`Ramification.Padic.artinConductorOfQuotient`). The finite theorem
`Ramification.Padic.exists_nat_artinConductorOfQuotient` (`ArtinExponent`, from
`finiteGaloisConductorIntegrality`) makes them natural numbers. A continuous representation has a
presentation (`HerbrandBridge.continuousWeilFiniteInertiaPresentation`), and the inertia
restriction to every finite Galois subextension is surjective
(`HerbrandBridge.weilInertiaRestriction_surjective`).
-/

namespace Langlands.Henniart

open Ramification.Padic Weil.Local

universe uF uV

section Presentation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}

/-- The Artin expression of a finite inertia presentation is a natural number. -/
theorem exists_nat_presentation_artinConductor (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    ∃ a : ℕ, P.artinConductor hP = (a : ℚ) :=
  exists_nat_artinConductorOfQuotient (absoluteFiniteExtension F P.extension).canonicalTopologicalData
    F.Carrier _ hP _ P.kernel_le

/-- The Swan expression of a finite inertia presentation is a natural number. -/
theorem exists_nat_presentation_swanConductor (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    ∃ s : ℕ, P.swanConductor hP = (s : ℚ) :=
  exists_nat_swanConductorOfQuotient (absoluteFiniteExtension F P.extension).canonicalTopologicalData
    F.Carrier _ hP _ P.kernel_le

end Presentation

/-- **Integrality for every presentation of every Weil representation**, and existence of an
integral presentation for every continuous one. -/
theorem weilConductorIntegrality : WeilConductorIntegralityStatement.{uF, uV} := by
  intro p _ F A
  refine ⟨fun P hP => ⟨exists_nat_presentation_artinConductor P hP,
    exists_nat_presentation_swanConductor P hP⟩, fun hA => ?_⟩
  obtain ⟨P⟩ := Ramification.HerbrandBridge.continuousWeilFiniteInertiaPresentation F A hA
  have hP := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F P.extension
  obtain ⟨a, ha⟩ := exists_nat_presentation_artinConductor P hP
  obtain ⟨s, hs⟩ := exists_nat_presentation_swanConductor P hP
  exact ⟨P, hP, a, s, ha, hs⟩

end Langlands.Henniart
