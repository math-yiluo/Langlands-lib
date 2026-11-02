import Langlands.AbelianScheme.PolarizedFiniteLevel.SixfoldPolarizationDegreeReductionStatement
import Langlands.AlgebraicGeometry.FiniteFlatConstantRankCompositionProof

/-! # Conditional native degree of the sixfold polarization -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Compose the assumed native degree of multiplication by six with the
datum's polarization degree. -/
theorem sixfoldPolarizationDegreeReduction :
    SixfoldPolarizationDegreeReductionStatement.{u} := by
  intro P K _ g d n a hfinite hflat hdegree
  let : IsFinite (hom ((6 : ℕ) • 𝟙 a.abelian)) := hfinite
  let : Flat (hom ((6 : ℕ) • 𝟙 a.abelian)) := hflat
  let : IsFinite (hom a.polarization) := a.polarized.1.1
  let : Flat (hom a.polarization) := a.polarized.1.2.1
  let : IsLocallyNoetherian (a.dualWitness.dual P).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (a.dualWitness.dual P).X.hom
  have hcomp : hom ((6 : ℕ) • 𝟙 a.abelian) ≫ hom a.polarization =
      hom (6 • a.polarization) := by
    rw [← hom_comp, Preadditive.nsmul_comp, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcomp]
    infer_instance
  · rw [← hcomp]
    infer_instance
  · have h := Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition
      a.abelian.X.left a.abelian.X.left (a.dualWitness.dual P).X.left
      (hom ((6 : ℕ) • 𝟙 a.abelian)) (hom a.polarization)
      (6 ^ (2 * g)) (d ^ 2) hdegree a.degree
    simpa only [HasConstantDegree, hcomp] using h

end Langlands.AbelianScheme.PolarizedFiniteLevel
