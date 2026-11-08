import Langlands.Representation.RankinSelberg.HighlyRamified.DualPointwise
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral

/-!
# Smearing along the last lower row

For `x` in the row space `F^(1 × (m+1))`, `ū_x = [[I,0],[x,1]]` in `GL_(m+2)`. For a smooth
representation and a locally constant compactly supported weight `S`, the finite algebraic
integral `∫ S(x) ρ(ū_x) v dx` is a vector of the representation; every linear functional
evaluates it as the scalar integral.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF uV

variable {F : Type uF} [Field F] {m : ℕ}

/-- The lower unipotent matrix `ū_x = [[I,0],[x,1]]`. -/
def lowerRow (x : Matrix (Fin 1) (Fin (m + 1)) F) : GeneralLinear (m + 1 + 1) F :=
  lowerBlockPair 1 x 1

theorem lowerRow_add (x y : Matrix (Fin 1) (Fin (m + 1)) F) :
    lowerRow (x + y) = lowerRow x * lowerRow y := by
  rw [lowerRow, lowerRow, lowerRow, lowerBlockPair_mul_lowerBlockPair]
  simp

theorem lowerRow_zero : lowerRow (0 : Matrix (Fin 1) (Fin (m + 1)) F) = 1 := by
  apply Units.ext
  change (Matrix.fromBlocks (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 0
      ((1 : lowerTriangularSubgroup 1 F).val.val)).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm = 1
  simp [Matrix.fromBlocks_one]

theorem lowerBlockPair_one_eq_mul_lowerRow (A : GeneralLinear (m + 1) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) :
    (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F) = rankInclusion 1 A * lowerRow x :=
  lowerBlockPair_eq_rankInclusion_mul A x 1

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_lowerRow : Continuous (lowerRow (F := F) (m := m)) :=
  continuous_lowerBlockPair.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem lowerRow_orbit_locallyConstant (ρ : Representation ℂ (GeneralLinear (m + 1 + 1) F) V)
    (hρ : IsSmooth ρ) (v : V) : IsLocallyConstant (fun x => ρ (lowerRow x) v) :=
  (Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous continuous_lowerRow

variable [MeasurableSpace (Matrix (Fin 1) (Fin (m + 1)) F)]
  [OpensMeasurableSpace (Matrix (Fin 1) (Fin (m + 1)) F)]

/-- The smearing integrand `x ↦ S(x) ρ(ū_x) v` as a finite-image simple function. -/
def lowerRowIntegrand (ρ : Representation ℂ (GeneralLinear (m + 1 + 1) F) V) (hρ : IsSmooth ρ)
    (S : Matrix (Fin 1) (Fin (m + 1)) F → ℂ) (hS : IsLocallyConstant S)
    (hSc : HasCompactSupport S) (v : V) : SimpleFunc (Matrix (Fin 1) (Fin (m + 1)) F) V :=
  compactlySupportedSimpleFunc (fun x => S x • ρ (lowerRow x) v)
    (hS.comp₂ (lowerRow_orbit_locallyConstant ρ hρ v) (· • ·)) hSc.smul_right

/-- The smeared vector `∫ S(x) ρ(ū_x) v dx`. -/
def lowerRowSmear (μ : Measure (Matrix (Fin 1) (Fin (m + 1)) F))
    (ρ : Representation ℂ (GeneralLinear (m + 1 + 1) F) V) (hρ : IsSmooth ρ)
    (S : Matrix (Fin 1) (Fin (m + 1)) F → ℂ) (hS : IsLocallyConstant S)
    (hSc : HasCompactSupport S) (v : V) : V :=
  AlgebraicIntegral.integral μ (lowerRowIntegrand ρ hρ S hS hSc v)

/-- Every linear functional evaluates the smeared vector as a scalar integral. -/
theorem lowerRowSmear_dual (μ : Measure (Matrix (Fin 1) (Fin (m + 1)) F))
    [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear (m + 1 + 1) F) V) (hρ : IsSmooth ρ)
    (S : Matrix (Fin 1) (Fin (m + 1)) F → ℂ) (hS : IsLocallyConstant S)
    (hSc : HasCompactSupport S) (v : V) (L : V →ₗ[ℂ] ℂ) :
    L (lowerRowSmear μ ρ hρ S hS hSc v) = ∫ x, S x * L (ρ (lowerRow x) v) ∂μ := by
  have hfin : (lowerRowIntegrand ρ hρ S hS hSc v).FinMeasSupp μ :=
    compactlySupportedSimpleFunc_finMeasSupp μ _ _ _
  unfold lowerRowSmear
  rw [← AlgebraicIntegral.integral_linearMap _ hfin L,
    AlgebraicIntegral.integral_eq_bochner _ (hfin.map L.map_zero)]
  congr 1
  funext x
  simp [lowerRowIntegrand]

end Langlands.RankinSelberg.HighlyRamified
