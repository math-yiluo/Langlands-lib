import Langlands.Group.GL.BruhatChartTangentFields
import Langlands.Group.GL.BruhatCellLocalChart
import Langlands.Representation.Archimedean.BruhatChartCasimir

/-! # Local vanishing at every point of a lower Bruhat cell -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Function Set Filter TopologicalSpace
open Langlands.Analysis Langlands.GeneralLinear Langlands.HarmonicAnalysis
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

namespace Langlands.Archimedean

universe u

variable {F : Type u} [RCLike F] {r : ℕ} {w : Equiv.Perm (Fin (r + 1))}

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) F
local notation "D" => 𝓓(matrixUnitsOpen F (r + 1), ℂ)
local notation "B" => upperTriangularSubgroup (r + 1) F
local notation "V" => permutationUnipotentMinus (r + 1) F w
local notation "P" => permutation (r + 1) F w
local notation "Xcoord" => (bruhatUpperSpace F (r + 1) × bruhatInversionSpace F w)
local notation "Nspace" => bruhatNormalSpace F w

private theorem vanishing_neighborhood_of_bruhatCellChart
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (a b : ℝ) (ψ : UnitaryAdditiveCharacter F)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z))
    (T : D →L[ℂ] ℂ) (eigenvalue : ℂ)
    (hCas : ∀ f : D, T (matrixTraceTestCasimir F (r + 1) f) = eigenvalue * T f)
    (hCov : ∀ (u : upperUnipotent (r + 1) F) (f : D),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * T f)
    (q : OpenPartialHomeomorph (Xcoord × Y × ℝ) M)
    (hqSmooth : ContDiffOn ℝ ∞ q q.source) (hqInv : ContDiffOn ℝ ∞ q.symm q.target)
    (hqΩ : q.target ⊆ matrixUnitsOpen F (r + 1))
    (hqCell : ∀ z ∈ q.source, q z ∈ bruhatCellMatrixSet F w ↔ z.2 = 0)
    (hqTrans : ∀ z ∈ q.source, fderiv ℝ q z (0, 0, 1) =
      (matrixWhittakerNormalPart (F := F) w a b).val * q z)
    (hqT : Distribution.IsVanishingOn T (q.target \ bruhatCellMatrixSet F w))
    (hq₀ : 0 ∈ q.source) :
    ∃ U : Set M, IsOpen U ∧ q 0 ∈ U ∧ U ⊆ q.target ∧ Distribution.IsVanishingOn T U := by
  have : FiniteDimensional ℝ Xcoord := FiniteDimensional.trans ℝ F Xcoord
  apply matrixDistribution_bruhatChart_vanishing_neighborhood (X := Xcoord) (Y := Y)
    w a b ψ hψ T eigenvalue hCas hCov q
  · exact hqSmooth
  · exact hqInv
  · exact hqΩ
  · exact hqCell
  · intro A hA x hx
    apply bruhatChart_tangent_of_cellSlice (F := F) (Y := Y × ℝ) w q
    · exact hqInv
    · exact hqCell
    · exact hA
    · exact hx
  · exact hqTrans
  · exact hqT
  · exact hq₀

/-- When the distribution is supported on a lower Bruhat cell in an
open neighborhood, the scalar Casimir equation forces local vanishing
at the given cell point. -/
theorem matrixDistribution_vanishing_near_lowerBruhatCell
    (hw : w ≠ Fin.revPerm) (a b : ℝ) (ψ : UnitaryAdditiveCharacter F)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z))
    (hc : a • (1 : F) - b • (RCLike.I : F) ≠ 0)
    (T : D →L[ℂ] ℂ) (eigenvalue : ℂ)
    (hCas : ∀ f : D, T (matrixTraceTestCasimir F (r + 1) f) = eigenvalue * T f)
    (hCov : ∀ (u : upperUnipotent (r + 1) F) (f : D),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * T f)
    (g : B) (v : V) {O : Set M} (hO : IsOpen O) (hOΩ : O ⊆ matrixUnitsOpen F (r + 1))
    (h0 : g.val.val * (P * v.val).val ∈ O)
    (hT : Distribution.IsVanishingOn T (O \ bruhatCellMatrixSet F w)) :
    ∃ U : Set M, IsOpen U ∧ g.val.val * (P * v.val).val ∈ U ∧ U ⊆ O ∧
      Distribution.IsVanishingOn T U := by
  let N := matrixWhittakerNormalPart (F := F) w a b
  have hN : N ≠ 0 := matrixWhittakerNormalPart_ne_zero w a b hw hc
  obtain ⟨Y, ynorm, yspace, ydim, q, hqCenter, hq₀, hqO, hqSmooth, hqInv, hqCell, hqTrans⟩ :=
    exists_bruhatCellLocalChart w g v N hN hO h0
  let norm : NormedAddCommGroup Y := ynorm
  let space : NormedSpace ℝ Y := yspace
  have : FiniteDimensional ℝ Y := ydim
  have hqΩ : q.target ⊆ matrixUnitsOpen F (r + 1) := hqO.trans hOΩ
  have hqT : Distribution.IsVanishingOn T (q.target \ bruhatCellMatrixSet F w) := by
    apply hT.mono
    intro y hy
    exact ⟨hqO hy.1, hy.2⟩
  suffices h : ∃ U : Set M, IsOpen U ∧ q 0 ∈ U ∧ U ⊆ q.target ∧ Distribution.IsVanishingOn T U by
    obtain ⟨U, hU, hU0, hUsub, hUT⟩ := h
    exact ⟨U, hU, hqCenter ▸ hU0, hUsub.trans hqO, hUT⟩
  apply vanishing_neighborhood_of_bruhatCellChart (F := F) (w := w) (Y := Y)
    a b ψ hψ T eigenvalue hCas hCov q
  · exact hqSmooth
  · exact hqInv
  · exact hqΩ
  · exact hqCell
  · exact hqTrans
  · exact hqT
  · exact hq₀

end Langlands.Archimedean
