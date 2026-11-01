import Langlands.Representation.GodementJacquet.SupercuspidalCutoffOutputSpan

/-! # Extending Fourier-regular pairing identities to arbitrary tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance extensionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance extensionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance extensionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance extensionT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance extensionDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance extensionMeasurable : MeasurableSpace F.Carrier := borel _
local instance extensionBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance extensionGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance extensionGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hsd : IsSelfDual ψ ν)

/-- Restriction of bilinear matrix-test/vector pairings to the actual
Fourier-regular test submodule. -/
def fourierRegularMatrixPairingRestriction :
    (SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ]
      V →ₗ[ℂ] W) →ₗ[ℂ]
    (fourierRegularMatrixTests (m + 1) ψ ν hsd →ₗ[ℂ] V →ₗ[ℂ] W) where
  toFun B := B.comp (fourierRegularMatrixTests (m + 1) ψ ν hsd).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem fourierRegularMatrixPairingRestriction_apply
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) (w : V) :
    fourierRegularMatrixPairingRestriction F ψ ν hsd B Φ w = B Φ.val w := rfl

variable (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
  (hρ : IsSupercuspidal ρ) (hi : ρ.IsIrreducible) (hm : 0 < m)
  (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F.Carrier).toMonoidHom))

include hρ hi hm hι in
/-- A translation-compatible bilinear pairing vanishing on Fourier-regular
tests vanishes on every full-matrix test and every vector. -/
theorem matrixPairing_eq_zero_of_fourierRegular
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F.Carrier),
      F.canonicalTopologicalData.determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (hz : fourierRegularMatrixPairingRestriction F ψ ν hsd B = 0) :
    B = 0 := by
  apply LinearMap.ext
  intro Φ
  apply LinearMap.ext
  intro w
  have hle : supercuspidalCutoffOutputSpan F ρ hρ ≤ (B Φ).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ℓ, hℓ, v, x, rfl⟩
    change B Φ (Hecke.integratedAction (generalLinearHaar F.Carrier m) ρ hρ.1.1
      (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) x) = 0
    rw [← supercuspidalConjugateMatrixSmoothing_pairing F ρ hρ ℓ hℓ B hB]
    let Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd :=
      ⟨supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v,
        supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests
          F ρ hρ ℓ hℓ hm hι ψ ν hsd Φ v⟩
    exact congrArg (fun T => T Ψ x) hz
  have hw : w ∈ supercuspidalCutoffOutputSpan F ρ hρ := by
    rw [supercuspidalCutoffOutputSpan_eq_top F ρ hρ hi]
    trivial
  exact hle hw

include hρ hi hm hι in
/-- Equality of two norm-one translation-compatible pairings is determined by
their restrictions to Fourier-regular matrix tests. -/
theorem matrixPairing_eq_of_fourierRegular
    (B D : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F.Carrier),
      F.canonicalTopologicalData.determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (hD : ∀ (g : GeneralLinear (m + 1) F.Carrier),
      F.canonicalTopologicalData.determinantNorm (m + 1) g = 1 →
      ∀ Φ w, D (rectangularTranslate g Φ) w = D Φ (ρ g⁻¹ w))
    (heq : fourierRegularMatrixPairingRestriction F ψ ν hsd B =
      fourierRegularMatrixPairingRestriction F ψ ν hsd D) :
    B = D := by
  apply sub_eq_zero.mp
  apply matrixPairing_eq_zero_of_fourierRegular F ψ ν hsd ρ hρ hi hm hι (B - D)
  · intro g hg Φ w
    simp only [LinearMap.sub_apply, hB g hg, hD g hg]
  · rw [map_sub, heq, sub_self]

end Langlands.GodementJacquet.Padic
