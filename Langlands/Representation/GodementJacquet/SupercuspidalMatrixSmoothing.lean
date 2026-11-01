import Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity
import Langlands.HarmonicAnalysis.RectangularTestSmooth
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.Induction.InverseTranspose

/-! # Compact coefficient smoothing of arbitrary matrix tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance smoothingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance smoothingValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance smoothingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance smoothingT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance smoothingDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance smoothingMeasurable : MeasurableSpace F.Carrier := borel _
local instance smoothingBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance smoothingGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance smoothingGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
  (hρ : IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- The determinant-unit coefficient cutoff, restricted to the actual group. -/
def supercuspidalCutoffGroupTest :
    V →ₗ[ℂ] SchwartzBruhat (GeneralLinear (m + 1) F.Carrier) :=
  (regularMatrixTestRestriction (m + 1)).comp
    ((supercuspidalCutoffMatrixTest F.canonicalTopologicalData
      (Nat.succ_pos m) ρ hρ ℓ hℓ).codRestrict (regularMatrixTests (m + 1))
        (supercuspidalCutoffMatrixTest_singular F.canonicalTopologicalData
          (Nat.succ_pos m) ρ hρ ℓ hℓ))

@[simp]
theorem supercuspidalCutoffGroupTest_apply (v : V)
    (g : GeneralLinear (m + 1) F.Carrier) :
    supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g =
      supercuspidalCutoffMatrixTest F.canonicalTopologicalData
        (Nat.succ_pos m) ρ hρ ℓ hℓ v g.val := rfl

/-- Compact smoothing by the inverse cutoff, using the smooth representation
on actual matrix Schwartz--Bruhat functions. -/
def supercuspidalMatrixSmoothing
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier)) :
    V →ₗ[ℂ] SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) :=
  ((Hecke.integratedAction (generalLinearHaar F.Carrier m)
    (rectangularSchwartzRepresentation (K := F.Carrier) (r := m + 1) (s := m + 1))
    rectangularSchwartzRepresentation_isSmooth).flip Φ).comp
      ((Hecke.TestFunction.inversion.toLinearMap).comp
        (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ))

theorem supercuspidalMatrixSmoothing_apply
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v =
      Hecke.integratedAction (generalLinearHaar F.Carrier m)
        (rectangularSchwartzRepresentation (K := F.Carrier)
          (r := m + 1) (s := m + 1))
        rectangularSchwartzRepresentation_isSmooth
        (Hecke.TestFunction.inversion (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v))
        Φ := rfl

/-- Determinant-unit translation of the coefficient vector becomes right
matrix translation of the smoothed test. -/
theorem supercuspidalMatrixSmoothing_right
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) (a : GeneralLinear (m + 1) F.Carrier)
    (ha : F.canonicalTopologicalData.determinantNorm (m + 1) a = 1) :
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
    exact supercuspidalCutoffMatrixTest_right F.canonicalTopologicalData
      (Nat.succ_pos m) ρ hρ ℓ hℓ v a ha (g⁻¹).val
  rw [supercuspidalMatrixSmoothing_apply, hcut,
    Hecke.integratedAction_leftTranslate]
  rfl

/-- Fourier evaluation obeys the inverse-transpose right covariance. -/
theorem supercuspidalMatrixSmoothing_fourier_right
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) (a : GeneralLinear (m + 1) F.Carrier)
    (ha : F.canonicalTopologicalData.determinantNorm (m + 1) a = 1)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) :
    rectangularFourierIntegral ψ ν
        (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ (ρ a v)) A =
      rectangularFourierIntegral ψ ν
        (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v)
        (A * (inverseTranspose (m + 1) F.Carrier a).val) := by
  rw [supercuspidalMatrixSmoothing_right F ρ hρ ℓ hℓ Φ v a ha]
  change rectangularFourierIntegral ψ ν
    (fun X => supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v (X * a.val)) A = _
  simpa only [rectangularTranslate_apply, Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_comp_mul_mul F.canonicalTopologicalData ψ ν
      1 a (map_one _) ha (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v) A

/-- Jacquet vanishing for the inverse-transpose pullback makes the original
smoothed test vanish at every singular matrix. -/
theorem supercuspidalMatrixSmoothing_singular (hm : 0 < m)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F.Carrier).toMonoidHom))
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier)
    (hA : ¬ IsUnit A) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v A = 0 := by
  obtain ⟨B, c, hB, hstab⟩ := exists_singular_inverseTranspose_stabilizer hm A hA
  let σ := ρ.comp (inverseTranspose (m + 1) F.Carrier).toMonoidHom
  let ev : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => Ψ A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L : V →ₗ[ℂ] ℂ := ev.comp (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ)
  have hL (g : B.conjugateUnipotent c) : L ∘ₗ σ g = L := by
    ext w
    change supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ
      (ρ (inverseTranspose (m + 1) F.Carrier g.val) w) A =
      supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ w A
    have hg : F.canonicalTopologicalData.determinantNorm (m + 1)
        (inverseTranspose (m + 1) F.Carrier g.val) = 1 := by
      rw [F.canonicalTopologicalData.determinantNorm_inverseTranspose,
        determinantNorm_eq_one_of_mem_conjugateUnipotent F.canonicalTopologicalData
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
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier)
    (hA : ¬ IsUnit A) :
    rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd
      (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v) A = 0 := by
  obtain ⟨B, c, hB, hstab⟩ := exists_singular_inverseTranspose_stabilizer hm A hA
  let ev : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ] ℂ :=
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
      (determinantNorm_eq_one_of_mem_conjugateUnipotent F.canonicalTopologicalData
        B c g.property), hstab g.val g.property]
  let := hρ.2 B hB c
  have hz : Jacquet.mk ρ (B.conjugateUnipotent c) v = 0 := Subsingleton.elim _ _
  have h := congrArg (Jacquet.lift ρ (B.conjugateUnipotent c) L hL) hz
  change L v = 0
  simpa only [Jacquet.lift_mk, map_zero] using h

/-- Compact coefficient smoothing takes every matrix test, without any support
restriction on that input, into the Fourier-regular test space. -/
theorem supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests (hm : 0 < m)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) :
    supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ Φ v ∈
      fourierRegularMatrixTests (m + 1) ψ ν hsd :=
  ⟨supercuspidalMatrixSmoothing_singular F ρ hρ ℓ hℓ hm hι Φ v,
    supercuspidalMatrixSmoothing_fourier_singular F ρ hρ ℓ hℓ hm ψ ν hsd Φ v⟩

end Langlands.GodementJacquet.Padic
