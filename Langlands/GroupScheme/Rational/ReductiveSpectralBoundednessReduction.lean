import Langlands.GroupScheme.Rational.DenseSpectralBoundedness
import Langlands.GroupScheme.IntegralModel
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension

/-! # The exact reductive spectral criterion from rational density -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

private theorem infinite_of_nontrivialValuativeRel
    (F : Type u) [Field F] [ValuativeRel F] [ValuativeRel.IsNontrivial F] :
    Infinite F := by
  obtain ⟨c, hc0, hc1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective c
  apply Infinite.of_injective (fun n : ℕ => a ^ n)
  intro m n h
  apply pow_right_injective₀ hc0 (ne_of_lt hc1)
  simpa only [map_pow, ha] using congrArg (ValuativeRel.valuation F) h

/-- The unchanged exact reductive rational-density statement supplies the last
input to the unchanged exact local-field spectral boundedness statement. -/
def ReductiveSpectralBoundednessReductionStatement : Prop :=
  ReductiveRationalPointDensityStatement.{u} → ReductiveSpectralBoundednessStatement.{u}

/-- All spectral boundedness steps are discharged here; the only explicit
remaining input is the independently specified rational-density proposition. -/
theorem reductiveSpectralBoundednessReduction :
    ReductiveSpectralBoundednessReductionStatement.{u} := by
  intro hdensity F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Infinite F := infinite_of_nontrivialValuativeRel F
  intro N ρ hc hint
  let α := baseChangeSectionHom (toAlgebraicClosure F) G
  have hα : ∀ g : rationalPoints G,
      α g = geometricRationalPoint (K := AlgebraicClosure F) G.X g := by
    intro g
    apply Over.OverMorphism.ext
    rw [baseChangeSectionHom_left]
    rfl
  apply isAlgebraicallyBounded_of_dense_geometricPointHom F G hG N ρ hc hint α hα
  have hd := hasDenseGeometricRationalPoints_of_hasDenseRationalPoints
    (K := AlgebraicClosure F) G.X (hdensity F G hG)
  change Dense (⋃ g : rationalPoints G, Set.range (α g).left)
  simp only [hα]
  change HasDenseGeometricRationalPoints F (AlgebraicClosure F) G.X
  exact hd

end Langlands.GroupScheme
