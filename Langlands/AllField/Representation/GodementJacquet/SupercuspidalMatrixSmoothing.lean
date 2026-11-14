import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothing
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity
import Langlands.AllField.Representation.Induction.InverseTranspose
/-! # Compact coefficient smoothing of arbitrary matrix tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding smoothingBorel smoothingDisconnected smoothingGLBorel smoothingGLMeasurable smoothingLocalField smoothingMeasurable smoothingT2 smoothingTopology smoothingValuativeRel supercuspidalCutoffGroupTest supercuspidalCutoffGroupTest_apply supercuspidalMatrixSmoothing supercuspidalMatrixSmoothing_apply supercuspidalMatrixSmoothing_fourier_right supercuspidalMatrixSmoothing_fourier_singular supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalMatrixSmoothing_right supercuspidalMatrixSmoothing_singular
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement equalRankFrobenius lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance smoothingT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance smoothingDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance smoothingMeasurable : MeasurableSpace F := borel _
local instance smoothingBorel : BorelSpace F := ⟨rfl⟩
local instance smoothingGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance smoothingGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
  (hρ : IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- The determinant-unit coefficient cutoff, restricted to the actual group. -/
def supercuspidalCutoffGroupTest :
    V →ₗ[ℂ] SchwartzBruhat (GeneralLinear (m + 1) F) :=
  (regularMatrixTestRestriction (m + 1)).comp
    ((supercuspidalCutoffMatrixTest (⟨⟩ : LocalFieldData F)
      (Nat.succ_pos m) ρ hρ ℓ hℓ).codRestrict (regularMatrixTests (m + 1))
        (supercuspidalCutoffMatrixTest_singular (⟨⟩ : LocalFieldData F)
          (Nat.succ_pos m) ρ hρ ℓ hℓ))

@[simp]
theorem supercuspidalCutoffGroupTest_apply (v : V)
    (g : GeneralLinear (m + 1) F) :
    supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g =
      supercuspidalCutoffMatrixTest (⟨⟩ : LocalFieldData F)
        (Nat.succ_pos m) ρ hρ ℓ hℓ v g.val := rfl

/-- Compact smoothing by the inverse cutoff, using the smooth representation
on actual matrix Schwartz--Bruhat functions. -/
def supercuspidalMatrixSmoothing
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F)) :
    V →ₗ[ℂ] SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
  ((Hecke.integratedAction (generalLinearHaar F m)
    (rectangularSchwartzRepresentation (K := F) (r := m + 1) (s := m + 1))
    rectangularSchwartzRepresentation_isSmooth).flip Φ).comp
      ((Hecke.TestFunction.inversion.toLinearMap).comp
        (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ))

theorem supercuspidalMatrixSmoothing_apply
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v =
      Hecke.integratedAction (generalLinearHaar F m)
        (rectangularSchwartzRepresentation (K := F)
          (r := m + 1) (s := m + 1))
        rectangularSchwartzRepresentation_isSmooth
        (Hecke.TestFunction.inversion (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v))
        Φ := rfl

/-- Determinant-unit translation of the coefficient vector becomes right
matrix translation of the smoothed test. -/
theorem supercuspidalMatrixSmoothing_right
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) (a : GeneralLinear (m + 1) F)
    (ha : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) a = 1) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ (ρ a v) =
      rectangularTranslate a (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v) := by
  have hcut :
      Hecke.TestFunction.inversion (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ (ρ a v)) =
        Hecke.TestFunction.leftTranslate a
          (Hecke.TestFunction.inversion (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v)) := by
    apply Hecke.TestFunction.ext
    intro g
    simp only [Hecke.TestFunction.inversion_apply, Hecke.TestFunction.leftTranslate_apply,
      supercuspidalCutoffGroupTest_apply, mul_inv_rev, inv_inv]
    exact supercuspidalCutoffMatrixTest_right (⟨⟩ : LocalFieldData F)
      (Nat.succ_pos m) ρ hρ ℓ hℓ v a ha (g⁻¹).val
  rw [supercuspidalMatrixSmoothing_apply, hcut,
    Hecke.integratedAction_leftTranslate]
  rfl

/-- Fourier evaluation obeys the inverse-transpose right covariance. -/
theorem supercuspidalMatrixSmoothing_fourier_right
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) (a : GeneralLinear (m + 1) F)
    (ha : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) a = 1)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    rectangularFourierIntegral ψ ν
        (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ (ρ a v)) A =
      rectangularFourierIntegral ψ ν
        (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v)
        (A * (inverseTranspose (m + 1) F a).val) := by
  rw [supercuspidalMatrixSmoothing_right F ρ hρ ℓ hℓ Φ v a ha]
  change rectangularFourierIntegral ψ ν
    (fun X => supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v (X * a.val)) A = _
  simpa only [rectangularTranslate_apply, Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_comp_mul_mul (⟨⟩ : LocalFieldData F) ψ ν
      1 a (map_one _) ha (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v) A

/-- Jacquet vanishing for the inverse-transpose pullback makes the original
smoothed test vanish at every singular matrix. -/
theorem supercuspidalMatrixSmoothing_singular (hm : 0 < m)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F).toMonoidHom))
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hA : ¬ IsUnit A) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v A = 0 := by
  obtain ⟨B, c, hB, hstab⟩ := exists_singular_inverseTranspose_stabilizer hm A hA
  let σ := ρ.comp (inverseTranspose (m + 1) F).toMonoidHom
  let ev : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => Ψ A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L : V →ₗ[ℂ] ℂ := ev.comp (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ)
  have hL (g : B.conjugateUnipotent c) : L ∘ₗ σ g = L := by
    ext w
    change supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ
      (ρ (inverseTranspose (m + 1) F g.val) w) A =
      supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ w A
    have hg : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1)
        (inverseTranspose (m + 1) F g.val) = 1 := by
      rw [(⟨⟩ : LocalFieldData F).determinantNorm_inverseTranspose,
        determinantNorm_eq_one_of_mem_conjugateUnipotent (⟨⟩ : LocalFieldData F)
          B c g.property, inv_one]
    rw [supercuspidalMatrixSmoothing_right F ρ hρ ℓ hℓ Φ w _ hg,
      rectangularTranslate_apply, hstab g.val g.property]
  let := hι.2 B hB c
  have hz : Jacquet.mk σ (B.conjugateUnipotent c) v = 0 := Subsingleton.elim _ _
  have h := congrArg (Jacquet.lift σ (B.conjugateUnipotent c) L hL) hz
  change L v = 0
  simpa only [Jacquet.lift_mk, map_zero] using h

/-- Jacquet vanishing of the original representation gives singular vanishing
of the actual Fourier transform of every smoothed test. -/
theorem supercuspidalMatrixSmoothing_fourier_singular (hm : 0 < m)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hA : ¬ IsUnit A) :
    rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd
      (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v) A = 0 := by
  obtain ⟨B, c, hB, hstab⟩ := exists_singular_inverseTranspose_stabilizer hm A hA
  let ev : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => Ψ A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L : V →ₗ[ℂ] ℂ := ev.comp
    ((rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd).toLinearMap.comp
      (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ))
  have hL (g : B.conjugateUnipotent c) : L ∘ₗ ρ g = L := by
    ext w
    change rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd
      (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ (ρ g.val w)) A =
      rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd
        (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ w) A
    simp only [rectangularFourierEquiv_apply]
    rw [supercuspidalMatrixSmoothing_fourier_right F ρ hρ ℓ hℓ ψ ν Φ w g.val
      (determinantNorm_eq_one_of_mem_conjugateUnipotent (⟨⟩ : LocalFieldData F)
        B c g.property), hstab g.val g.property]
  let := hρ.2 B hB c
  have hz : Jacquet.mk ρ (B.conjugateUnipotent c) v = 0 := Subsingleton.elim _ _
  have h := congrArg (Jacquet.lift ρ (B.conjugateUnipotent c) L hL) hz
  change L v = 0
  simpa only [Jacquet.lift_mk, map_zero] using h

/-- Compact coefficient smoothing takes every matrix test, without any support
restriction on that input, into the Fourier-regular test space. -/
theorem supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests (hm : 0 < m)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v ∈
      fourierRegularMatrixTests (m + 1) ψ ν hsd :=
  ⟨supercuspidalMatrixSmoothing_singular F ρ hρ ℓ hℓ hm hι Φ v,
    supercuspidalMatrixSmoothing_fourier_singular F ρ hρ ℓ hℓ hm ψ ν hsd Φ v⟩

end Langlands.AllField.GodementJacquet.Padic
