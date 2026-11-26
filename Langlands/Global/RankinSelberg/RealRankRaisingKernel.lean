import Langlands.Global.RankinSelberg.RealRankRaisingHaar
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Schwartz kernels from smooth functions on the real rank-raising subgroup -/

noncomputable section

open Filter Matrix Set
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral

open Langlands.GeneralLinear Langlands.LinearLieGroup
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)

local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "X" => fun r => Matrix (Fin 1) (Fin (r + 1)) ℝ
local notation "P" => fun r => X r × B
local notation "W" => fun r => X r × ℝ
local notation "M" => fun r => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℝ
local notation "H" => rankRaisingSubgroup
local notation "chart" => rankRaisingHomeomorph

/-- Lie algebra of the real rank-raising subgroup with its exponential charts. -/
abbrev rankRaisingLie (r : ℕ) : Submodule ℝ (M r) :=
  lieSubmodule (rankRaisingSubgroup r) (isClosed_rankRaisingSubgroup r)

/-- The exponential Lie structure on the group of compensating right translations. -/
theorem rankRaisingExpLie (r : ℕ) : IsExpLieAlgebra (H r) (rankRaisingLie r) :=
  isExpLieAlgebra_of_isClosed (H r) (isClosed_rankRaisingSubgroup r)

private local instance (r : ℕ) : ChartedSpace (rankRaisingLie r) (H r) :=
  (rankRaisingExpLie r).chartedSpace

private def oneBlock (h : ℝˣ) : B :=
  ⟨Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin 1 => h), by
    intro i j hij
    exact False.elim ((lt_irrefl i) ((Subsingleton.elim j i) ▸ hij))⟩

private theorem val_oneBlock (h : ℝˣ) : (oneBlock h).val.val = Matrix.diagonal (fun _ : Fin 1 => h.val) :=
  rfl

private theorem det_oneBlock (h : ℝˣ) : determinant (oneBlock h).val = h := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_oneBlock, Matrix.det_diagonal, Fin.prod_univ_one]

private theorem oneBlock_determinant (h : B) : oneBlock (determinant h.val) = h := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [val_oneBlock, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

private def coords {r : ℕ} (g : H r) : W r :=
  (((chart r).symm g).1, ((chart r).symm g).2.val.val.det)

private theorem continuous_coords (r : ℕ) : Continuous (coords (r := r)) := by
  have hc : Continuous (fun h : B => h.val.val) := Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous (fun p : P r => (p.1, p.2.val.val.det)) :=
    continuous_fst.prodMk (hc.matrix_det.comp continuous_snd)
  exact hcont.comp (chart r).symm.continuous

private def fromReal {r : ℕ} (p : W r) : H r :=
  if h : p.2 ≠ 0 then chart r (p.1, oneBlock (Units.mk0 p.2 h)) else 1

private theorem coords_fromReal {r : ℕ} (p : W r) (h : p.2 ≠ 0) : coords (fromReal p) = p := by
  rw [fromReal, dite_eq_left h, coords, (chart r).symm_apply_apply]
  refine Prod.ext rfl ?_
  change ((determinant (oneBlock (Units.mk0 p.2 h)).val : ℝˣ) : ℝ) = p.2
  rw [det_oneBlock]
  rfl

private theorem coords_snd_ne_zero {r : ℕ} (g : H r) : (coords g).2 ≠ 0 :=
  (determinant ((chart r).symm g).2.val).ne_zero

private theorem rankRaisingDiagonal_inv_val (r : ℕ) (h : ℝˣ) :
    (rankRaisingDiagonal r (oneBlock h))⁻¹.val =
      Matrix.diagonal (fun i => if i = 0 then h.val⁻¹ else 1) := by
  rw [rankRaisingDiagonal, det_oneBlock, ← map_inv, diagonalUnits_val]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

private def matrixFormula {r : ℕ} (p : W r) : M r :=
  (Matrix.fromBlocks (Matrix.diagonal (fun i : Fin (r + 1) => if i = 0 then p.2⁻¹ else 1))
    0 p.1 (Matrix.diagonal (fun _ : Fin 1 => p.2))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private theorem val_fromReal {r : ℕ} (p : W r) (h : p.2 ≠ 0) : (fromReal p).val.val = matrixFormula p := by
  rw [fromReal, dite_eq_left h, rankRaisingHomeomorph_apply_val]
  change (Matrix.fromBlocks (rankRaisingDiagonal r (oneBlock (Units.mk0 p.2 h)))⁻¹.val
    0 p.1 (oneBlock (Units.mk0 p.2 h)).val.val).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = _
  rw [rankRaisingDiagonal_inv_val, val_oneBlock]
  rfl

private theorem contDiffAt_matrixFormula {r : ℕ} (p : W r) (h : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ matrixFormula p := by
  let assemble : (Fin (r + 1 + 1) → Fin (r + 1 + 1) → ℝ) →L[ℝ] M r :=
    (Matrix.ofLinearEquiv ℝ).toLinearMap.toContinuousLinearMap
  have hp : ContDiffAt ℝ ∞ (fun q : W r => fun i j => matrixFormula q i j) p := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    rcases hi : finSumFinEquiv.symm i with i | i <;>
      rcases hj : finSumFinEquiv.symm j with j | j <;>
      simp only [matrixFormula, Matrix.submatrix_apply, hi, hj, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · by_cases he : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq]
        by_cases hz : i = 0
        · simp only [hz, ite_true]
          exact contDiffAt_snd.inv h
        · simp only [hz, ite_false]
          exact contDiffAt_const
      · simp only [Matrix.diagonal_apply_ne _ he]
        exact contDiffAt_const
    · exact contDiffAt_const
    · exact (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_fst
    · obtain rfl : i = j := Subsingleton.elim _ _
      simp only [Matrix.diagonal_apply_eq]
      exact contDiffAt_snd
  exact assemble.contDiff.contDiffAt.comp p hp

private theorem eventually_snd_ne_zero {r : ℕ} (p : W r) (h : p.2 ≠ 0) :
    ∀ᶠ q : W r in 𝓝 p, q.2 ≠ 0 :=
  (isOpen_ne.preimage continuous_snd).mem_nhds h

private theorem contMDiffAt_fromReal {r : ℕ} (p : W r) (h : p.2 ≠ 0) :
    ContMDiffAt 𝓘(ℝ, W r) 𝓘(ℝ, rankRaisingLie r) ∞ fromReal p := by
  apply (rankRaisingExpLie r).contMDiffAt_of_val
  apply ContDiffAt.contMDiffAt
  exact (contDiffAt_matrixFormula p h).congr_of_eventuallyEq
    ((eventually_snd_ne_zero p h).mono fun q hq => val_fromReal q hq)

private def kernelExtension {r : ℕ} (K : H r → ℂ) (p : W r) : ℂ :=
  if p.2 ≠ 0 then K (fromReal p) * (((|p.2| ^ (r + 2))⁻¹ : ℝ) : ℂ) else 0

private theorem support_kernelExtension {r : ℕ} (K : H r → ℂ) :
    Function.support (kernelExtension K) ⊆ coords '' tsupport K := by
  intro p hp
  by_cases h : p.2 ≠ 0
  · have hk : fromReal p ∈ Function.support K := by
      intro hz
      exact hp (by simp [kernelExtension, h, hz])
    exact ⟨fromReal p, subset_tsupport _ hk, coords_fromReal p h⟩
  · exact False.elim (hp (by simp [kernelExtension, h]))

private theorem contDiff_kernelExtension {r : ℕ} (K : H r → ℂ)
    (hK : ContMDiff 𝓘(ℝ, rankRaisingLie r) 𝓘(ℝ, ℂ) ∞ K) (hC : HasCompactSupport K) :
    ContDiff ℝ ∞ (kernelExtension K) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases h : p.2 ≠ 0
  · have hA : ContDiffAt ℝ ∞ (K ∘ fromReal) p :=
      ((hK (fromReal p)).comp p (contMDiffAt_fromReal p h)).contDiffAt
    have hW : ContDiffAt ℝ ∞ (fun q : W r => (|q.2| ^ (r + 2))⁻¹) p :=
      ((contDiffAt_snd.abs h).pow _).inv (pow_ne_zero _ (abs_ne_zero.mpr h))
    have hM : ContDiffAt ℝ ∞ (fun q : W r => K (fromReal q) * (((|q.2| ^ (r + 2))⁻¹ : ℝ) : ℂ)) p :=
      hA.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p hW)
    exact hM.congr_of_eventuallyEq ((eventually_snd_ne_zero p h).mono fun q hq =>
      ite_eq_left hq)
  · have hoc : IsOpen (coords '' tsupport K)ᶜ := (hC.image (continuous_coords r)).isClosed.isOpen_compl
    have hp : p ∈ (coords '' tsupport K)ᶜ := by
      rintro ⟨g, _, rfl⟩
      exact h (coords_snd_ne_zero g)
    have hEv : ∀ᶠ q in 𝓝 p, q ∈ (coords '' tsupport K)ᶜ := hoc.mem_nhds hp
    have hzero : kernelExtension K =ᶠ[𝓝 p] fun _ => 0 := hEv.mono
      (fun q hq => Function.notMem_support.mp (fun hq' => hq (support_kernelExtension K hq')))
    exact contDiffAt_const.congr_of_eventuallyEq hzero

private theorem kernelExtension_chart {r : ℕ} (K : H r → ℂ) (p : P r) :
    kernelExtension K (p.1, p.2.val.val.det) =
      K (chart r p) * ((rankRaisingLeftRelativeDensity r (chart r p) : ℝ) : ℂ) := by
  have h : p.2.val.val.det ≠ 0 := (determinant p.2.val).ne_zero
  have he : oneBlock (Units.mk0 p.2.val.val.det h) = p.2 := by
    have hu : Units.mk0 p.2.val.val.det h = determinant p.2.val := Units.ext rfl
    rw [hu, oneBlock_determinant]
  rw [kernelExtension, ite_eq_left h, fromReal, dite_eq_left h, he, rankRaisingLeftRelativeDensity,
    (chart r).symm_apply_apply, rankRaisingLeftDensity, trailingHeight, NNReal.coe_inv, NNReal.coe_pow,
    coe_nnnorm, Real.norm_eq_abs]

/-- A compact smooth kernel on the compensating subgroup, multiplied by its left-to-right
Haar density, extends by zero to a compactly supported Schwartz function of the full bottom row. -/
def RealRankRaisingKernelStatement : Prop :=
  ∀ (r : ℕ) (K : H r → ℂ), (letI := (rankRaisingExpLie r).chartedSpace;
      ContMDiff 𝓘(ℝ, rankRaisingLie r) 𝓘(ℝ, ℂ) ∞ K) → HasCompactSupport K →
    ∃ φ : 𝓢(W r, ℂ), HasCompactSupport φ ∧
      tsupport φ ⊆ {p : W r | p.2 ≠ 0} ∧
      ∀ p : P r, φ (p.1, p.2.val.val.det) =
        K (chart r p) * ((rankRaisingLeftRelativeDensity r (chart r p) : ℝ) : ℂ)

theorem realRankRaisingKernel : RealRankRaisingKernelStatement := by
  intro r K hK hC
  have hS : tsupport (kernelExtension K) ⊆ coords '' tsupport K :=
    closure_minimal (support_kernelExtension K) (hC.image (continuous_coords r)).isClosed
  have hComp : HasCompactSupport (kernelExtension K) :=
    (hC.image (continuous_coords r)).of_isClosed_subset isClosed_closure hS
  let φ := hComp.toSchwartzMap (contDiff_kernelExtension K hK hC)
  refine ⟨φ, hComp, fun p hp => ?_, kernelExtension_chart K⟩
  obtain ⟨g, _, rfl⟩ := hS hp
  exact coords_snd_ne_zero g

end Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral
