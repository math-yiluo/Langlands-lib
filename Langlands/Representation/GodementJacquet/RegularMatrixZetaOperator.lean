import Langlands.Representation.GodementJacquet.FourierRegularMatrixTests
import Langlands.Representation.GodementJacquet.CompactMatrixLaurent
import Langlands.Representation.Hecke.FiniteRankAction
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof

/-! # Actual zeta operators for regular matrix tests -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance regularMatrixZetaTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance regularMatrixZetaValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance regularMatrixZetaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance regularMatrixZetaT2Space : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance regularMatrixZetaTotallyDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance regularMatrixZetaGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance regularMatrixZetaGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The actual determinant weight is locally constant at every complex exponent. -/
theorem determinantWeight_locallyConstant (s : ℂ) :
    IsLocallyConstant (fun g : GeneralLinear (n + 1) F.Carrier =>
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s) := by
  simp_rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
  exact ((IsLocallyConstant.iff_continuous _).mpr
    ((continuous_ord_units F.canonicalTopologicalData).comp
      (F.canonicalTopologicalData.generalLinearDeterminant (n + 1)).continuous)).comp
        (fun m : ℤ => spectralPoint F.canonicalTopologicalData.residueCardinality s ^ m)

/-- Restrict a regular full-matrix test to GL and multiply by the actual
determinant weight, preserving compact support and local constancy. -/
def weightedRegularMatrixTest (s : ℂ) :
    regularMatrixTests (K := F.Carrier) (n + 1) →ₗ[ℂ]
      SchwartzBruhat (GeneralLinear (n + 1) F.Carrier) where
  toFun Φ :=
    ⟨fun g => Φ.val g.val *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s,
      ((regularMatrixTestRestriction (n + 1) Φ).locallyConstant).mul
        (determinantWeight_locallyConstant F s),
      (hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) Φ.property).mul_right⟩
  map_add' Φ Ψ := by
    apply Hecke.TestFunction.ext
    intro g
    exact add_mul _ _ _
  map_smul' c Φ := by
    apply Hecke.TestFunction.ext
    intro g
    exact mul_assoc c _ _

@[simp] theorem weightedRegularMatrixTest_apply (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (g : GeneralLinear (n + 1) F.Carrier) :
    weightedRegularMatrixTest F s Φ g =
      Φ.val g.val *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual compact integral operator for a regular matrix test, constructed
without any topology or completeness on the representation carrier. -/
def regularMatrixZetaOperator
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (s : ℂ) :
    regularMatrixTests (K := F.Carrier) (n + 1) →ₗ[ℂ] Module.End ℂ V :=
  (Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ).comp
    (weightedRegularMatrixTest F s)

/-- Every algebraic functional evaluates the operator as the actual matrix
integral, for the shared normalized group Haar measure. -/
theorem regularMatrixZetaOperator_dual
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) :
    ℓ (regularMatrixZetaOperator F ρ hρ s Φ v) =
      matrixIntegral F Φ.val s (fun g => ℓ (ρ g v)) := by
  rw [regularMatrixZetaOperator, LinearMap.comp_apply, Hecke.integratedAction_dual]
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [weightedRegularMatrixTest_apply, GodementJacquet.matrixIntegrand]
  ring

/-- These coefficient integrals converge absolutely at every exponent, even
for an arbitrary algebraic functional. -/
theorem regularMatrixZetaOperator_converges
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) :
    MatrixConverges F Φ.val s (fun g => ℓ (ρ g v)) := by
  have hc : IsLocallyConstant (fun g => ℓ (ρ g v)) :=
    (Hecke.orbitMap_locallyConstant ρ (hρ v)).comp ℓ
  have hi := ((weightedRegularMatrixTest F s Φ).locallyConstant.mul hc).continuous
    |>.integrable_of_hasCompactSupport
      (μ := generalLinearHaar F.Carrier n)
      (weightedRegularMatrixTest F s Φ).hasCompactSupport.mul_right
  apply hi.congr
  filter_upwards [] with g
  simp only [Pi.mul_apply, GodementJacquet.matrixIntegrand, weightedRegularMatrixTest_apply]
  ring

/-- Admissibility makes the actual regular-test zeta operator finite rank. -/
theorem regularMatrixZetaOperator_finiteDimensional_range
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsAdmissible ρ) (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1)) :
    FiniteDimensional ℂ
      (LinearMap.range (regularMatrixZetaOperator F ρ hρ.1 s Φ)) := by
  let := F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  let : TotallyDisconnectedSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin (n + 1) → Fin (n + 1) → F.Carrier))
  let : TotallyDisconnectedSpace (GeneralLinear (n + 1) F.Carrier) :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  exact Hecke.integratedAction_finiteDimensional_range
    (generalLinearHaar F.Carrier n) ρ hρ (weightedRegularMatrixTest F s Φ)

end Langlands.GodementJacquet.Padic
