import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDominantCoefficientBounds
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-! # The Xi upper bound conditional on actual Jacquet unipotence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

set_option maxHeartbeats 1500000

/-- The conditional intermediate target, retaining actual Jacquet unipotence
as its sole premise. -/
def RationalXiUpperBoundReductionStatement : Prop :=
  RationalMinimalInducedJacquetUnipotentStatement.{u} → RationalXiUpperBoundStatement.{u}

/-- The complete Xi upper bound from unipotence on the actual normalized
Jacquet modules of the minimal induction. -/
theorem rationalXiUpperBound_of_jacquetUnipotent :
    RationalMinimalInducedJacquetUnipotentStatement.{u} → RationalXiUpperBoundStatement.{u} := by
  intro hU F _ _ _ _ G _ _ hG S i hi ν hν K0 hBasis A q hA
    K hKo hKc hPK N _ ρ hρ
  let h := isSemidirectDecomposition_minimalStandard hG hi hν
  let π := (rationalMinimalInduced i ν h).representation
  have hπ : IsAdmissible π :=
    rationalMinimalInduced_isAdmissible h hKc hPK
      (continuous_projection_minimalStandard hG hi hν h)
  have hUnip : ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
      ∃ r : ℕ, ∀ x : Multiplicative (faceCocharacterLattice J),
        (Jacquet.normalizedActionOfModulus π
          (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
          (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
          (standardUnipotentModulus i ν J) (faceUniformizerPowers i ν J x) - 1) ^ r = 0 := by
    intro J hJ
    obtain ⟨r, hr⟩ := hU F G hG S i hi ν hν J hJ
    refine ⟨r, fun x => ?_⟩
    exact hr (faceUniformizerPowers i ν J x) fun m =>
      faceUniformizerPowers_central i ν (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν)
        J (standardCocharacter F G hG S i hi ν hν J hJ).1 x m
  obtain ⟨d, hd⟩ := exists_dominant_lattice_coefficient_bound hG hi hν hBasis ρ hρ π hπ hUnip
  refine ⟨d, fun g₁ g₂ => ?_⟩
  let v := π g₂ (rationalSphericalVector h hKo hKc hPK)
  let ell := smoothContragredient π g₁⁻¹ (rationalSphericalFunctional h hKo hKc)
  obtain ⟨C, -, hC⟩ := hd v ell
  refine ⟨C, fun a ha haC => ?_⟩
  obtain ⟨lam, halam, -, hlam⟩ :=
    hA.exists_eq_uniformizerPowers (Set.empty_subset _) haC
  have hcoeff :
      smoothDualPairing π ell (π a v) = ((rationalXi hKc hPK (g₁ * a * g₂) : ℝ) : ℂ) := by
    rw [rationalXi_eq_sphericalCoefficient h hKo hKc hPK]
    change smoothDualPairing π
      (smoothContragredient π g₁⁻¹ (rationalSphericalFunctional h hKo hKc))
      (π a (π g₂ (rationalSphericalVector h hKo hKc hPK))) =
        smoothDualPairing π (rationalSphericalFunctional h hKo hKc)
          (π (g₁ * a * g₂) (rationalSphericalVector h hKo hKc hPK))
    simp only [smoothDualPairing_action, inv_inv, map_mul, Module.End.mul_apply]
  have hreal : rationalXi hKc hPK (g₁ * a * g₂) ≤
      ‖smoothDualPairing π ell (π a v)‖ := by
    rw [hcoeff, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  have hb := (hreal.trans (by simpa only [halam] using hC lam hlam))
  have hpa : (⟨a, ha⟩ : standardParabolicPoints i ν ∅) =
      uniformizerPowersParabolic i ν (.ofAdd lam) := Subtype.ext halam
  rw [hpa]
  simpa only [halam] using hb

end Langlands.HarishChandraSchwartz
