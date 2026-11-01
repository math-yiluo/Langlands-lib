import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothing
import Langlands.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator
import Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral

/-! # Conjugate coefficient smoothing and bilinear transfer -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance transferTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance transferValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance transferLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance transferT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance transferDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance transferMeasurable : MeasurableSpace F.Carrier := borel _
local instance transferBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance transferGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance transferGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
  (hρ : IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- The complex conjugate of the actual compact coefficient cutoff on GL. -/
def conjugateSupercuspidalCutoffGroupTest (v : V) :
    SchwartzBruhat (GeneralLinear (m + 1) F.Carrier) :=
  ⟨fun g => starRingEnd ℂ (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g),
    (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v).locallyConstant.comp (starRingEnd ℂ),
    (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v).hasCompactSupport.comp_left
      (map_zero (starRingEnd ℂ))⟩

@[simp]
theorem conjugateSupercuspidalCutoffGroupTest_apply (v : V)
    (g : GeneralLinear (m + 1) F.Carrier) :
    conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g =
      starRingEnd ℂ (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g) := rfl

theorem conjugateSupercuspidalCutoffGroupTest_eq_zero (v : V)
    (g : GeneralLinear (m + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.determinantNorm (m + 1) g ≠ 1) :
    conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g = 0 := by
  simp only [conjugateSupercuspidalCutoffGroupTest_apply,
    supercuspidalCutoffGroupTest_apply,
    supercuspidalCutoffMatrixTest_apply_of_not_mem F.canonicalTopologicalData
      (Nat.succ_pos m) ρ hρ ℓ hℓ v g hg, map_zero]

/-- Smoothing by the conjugate coefficient, defined through pointwise
conjugation of the proved supercuspidal smoothing. -/
def supercuspidalConjugateMatrixSmoothing
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) :=
  conjugateMatrixTest (m + 1)
    (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ
      (conjugateMatrixTest (m + 1) Φ) v)

/-- This is the actual integrated action of the inverted conjugate cutoff. -/
theorem supercuspidalConjugateMatrixSmoothing_eq_integratedAction
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) :
    supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v =
      Hecke.integratedAction (generalLinearHaar F.Carrier m)
        (rectangularSchwartzRepresentation (K := F.Carrier)
          (r := m + 1) (s := m + 1))
        rectangularSchwartzRepresentation_isSmooth
        (Hecke.TestFunction.inversion
          (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v)) Φ := by
  ext X
  let ev : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => Ψ X, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change starRingEnd ℂ (ev
    (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ
      (conjugateMatrixTest (m + 1) Φ) v)) = ev _
  rw [supercuspidalMatrixSmoothing_apply, Hecke.integratedAction_dual,
    Hecke.integratedAction_dual, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [Hecke.TestFunction.inversion_apply,
    conjugateSupercuspidalCutoffGroupTest_apply, ev,
    LinearMap.coe_mk, AddHom.coe_mk,
    rectangularSchwartzRepresentation_apply, rectangularTranslate_apply,
    conjugateMatrixTest_apply, map_mul, starRingEnd_self_apply]

/-- Conjugated smoothing retains both singular-vanishing conditions. -/
theorem supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests
    (hm : 0 < m)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v : V) :
    supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v ∈
      fourierRegularMatrixTests (m + 1) ψ ν hsd :=
  conjugate_mem_fourierRegularMatrixTests (m + 1) ψ ν hsd
    (supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests
      F ρ hρ ℓ hℓ hm hι ψ ν hsd (conjugateMatrixTest (m + 1) Φ) v)

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A translation-compatible bilinear pairing commutes with compact smoothing
on determinant norm one. The proof uses only finite-fiber integration. -/
theorem compactMatrixSmoothing_pairing
    (hsm : IsSmooth ρ)
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F.Carrier),
      F.canonicalTopologicalData.determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (f : SchwartzBruhat (GeneralLinear (m + 1) F.Carrier))
    (hf : ∀ g, F.canonicalTopologicalData.determinantNorm (m + 1) g ≠ 1 → f g = 0)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (w : V) :
    B (Hecke.integratedAction (generalLinearHaar F.Carrier m)
      (rectangularSchwartzRepresentation (K := F.Carrier) (r := m + 1) (s := m + 1))
      rectangularSchwartzRepresentation_isSmooth (Hecke.TestFunction.inversion f) Φ) w =
      B Φ (Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hsm f w) := by
  let τ := rectangularSchwartzRepresentation
    (K := F.Carrier) (r := m + 1) (s := m + 1)
  let hτ : IsSmooth τ := rectangularSchwartzRepresentation_isSmooth
  let μ := generalLinearHaar F.Carrier m
  let : Measure.IsInvInvariant μ := (generalLinearHaarSymmetries F.Carrier m).1
  change (B.flip w) (AlgebraicIntegral.integral μ
      (Hecke.actionIntegrand τ hτ (Hecke.TestFunction.inversion f) Φ)) =
    B Φ (AlgebraicIntegral.integral μ (Hecke.actionIntegrand ρ hsm f w))
  rw [← AlgebraicIntegral.integral_linearMap _
      (Hecke.actionIntegrand_finMeasSupp μ τ hτ (Hecke.TestFunction.inversion f) Φ),
    ← AlgebraicIntegral.integral_linearMap _
      (Hecke.actionIntegrand_finMeasSupp μ ρ hsm f w)]
  rw [← AlgebraicIntegral.integral_comp_measurePreserving
    ((Hecke.actionIntegrand τ hτ (Hecke.TestFunction.inversion f) Φ).map (B.flip w))
    Inv.inv (Measure.measurePreserving_inv μ)]
  congr 1
  ext g
  change B ((Hecke.TestFunction.inversion f) g⁻¹ • τ g⁻¹ Φ) w =
    B Φ (f g • ρ g w)
  simp only [Hecke.TestFunction.inversion_apply, inv_inv, map_smul, LinearMap.smul_apply]
  by_cases hg : F.canonicalTopologicalData.determinantNorm (m + 1) g = 1
  · have hgi : F.canonicalTopologicalData.determinantNorm (m + 1) g⁻¹ = 1 := by
      rw [map_inv, hg, inv_one]
    simpa only [τ, rectangularSchwartzRepresentation_apply,
      inv_inv] using congrArg (fun z => f g • z) (hB g⁻¹ hgi Φ w)
  · simp [hf g hg]

/-- Both continued zeta pairings can use this same integrated rho output. -/
theorem supercuspidalConjugateMatrixSmoothing_pairing
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F.Carrier),
      F.canonicalTopologicalData.determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier))
    (v w : V) :
    B (supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v) w =
      B Φ (Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) w) := by
  rw [supercuspidalConjugateMatrixSmoothing_eq_integratedAction]
  exact compactMatrixSmoothing_pairing F ρ hρ.1.1 B hB _
    (conjugateSupercuspidalCutoffGroupTest_eq_zero F ρ hρ ℓ hℓ v) Φ w

end Langlands.GodementJacquet.Padic
