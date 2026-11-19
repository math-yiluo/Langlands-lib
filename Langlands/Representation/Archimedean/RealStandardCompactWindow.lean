import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Mathlib.Topology.ContinuousMap.Compact

/-! # Closed Fourier window for the smooth real standard module -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactWindow

variable {n : ℕ}

local notation "K" => unitaryCompact ℝ n

private def rotated (p : ℕ) (k : K) (θ : ℝ) : K :=
  ⟨blockRotation n p θ * k, (unitaryCompact ℝ n).mul_mem
    (blockRotation_mem_unitaryCompact n p θ) k.property⟩

private theorem continuous_rotated (p : ℕ) (k : K) : Continuous (rotated p k) :=
  ((continuous_blockRotation n p).mul continuous_const).subtype_mk _

private def integrand (p : ℕ) (j : ℤ) (k : K) (F : C(K, ℂ)) (θ : ℝ) : ℂ :=
  F (rotated p k θ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))

private theorem integrable_integrand (p : ℕ) (j : ℤ) (k : K) (F : C(K, ℂ)) :
    IntervalIntegrable (integrand p j k F) MeasureTheory.volume 0 (2 * Real.pi) :=
  ((F.continuous.comp (continuous_rotated p k)).mul
    (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _

private def fourierLinear (p : ℕ) (j : ℤ) (k : K) : C(K, ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∫ θ in (0 : ℝ)..2 * Real.pi, integrand p j k F θ
  map_add' F H := by
    simp only [integrand, ContinuousMap.add_apply, add_mul]
    exact intervalIntegral.integral_add (integrable_integrand p j k F)
      (integrable_integrand p j k H)
  map_smul' z F := by
    simp only [integrand, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
      intervalIntegral.integral_const_mul, RingHom.id_apply]

/-- Rotation Fourier evaluation at a point of `O(n)` in the supremum norm. -/
def fourier (p : ℕ) (j : ℤ) (k : K) : C(K, ℂ) →L[ℂ] ℂ :=
  (fourierLinear p j k).mkContinuous (2 * Real.pi) fun F => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 2 * Real.pi) (C := ‖F‖) (f := integrand p j k F)
      (fun θ _ => by
        have hExp : ‖Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))‖ = 1 := by
          rw [Complex.norm_exp]
          simp
        rw [integrand, norm_mul, hExp, mul_one]
        exact F.norm_coe_le_norm (rotated p k θ))
    change ‖∫ θ in (0 : ℝ)..2 * Real.pi, integrand p j k F θ‖ ≤ _
    rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
    exact h.trans_eq (mul_comm ‖F‖ (2 * Real.pi))

/-- The low rotation modes of a compact function vanish in every induced block. -/
def window (n : ℕ) (ds : List RealBlock) : Submodule ℂ C(unitaryCompact ℝ n, ℂ) :=
  ⨅ (p : ℕ) (d : ComplexCharacterData) (_ : realInducedBlockAt ds p = some d)
    (j : ℤ) (_ : |j| < |d.weight|) (k : unitaryCompact ℝ n), (fourier p j k).ker

theorem isClosed_window (n : ℕ) (ds : List RealBlock) :
    IsClosed (window n ds : Set C(unitaryCompact ℝ n, ℂ)) := by
  simp only [window, Submodule.coe_iInf]
  exact isClosed_iInter fun p => isClosed_iInter fun d => isClosed_iInter fun _ =>
    isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun k =>
      (fourier (n := n) p j k).isClosed_ker

/-- Restriction of a smooth position principal-series vector to the compact subgroup. -/
def restrict (n : ℕ) (ds : List RealBlock) :
    principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] C(unitaryCompact ℝ n, ℂ) where
  toFun f := ⟨fun k => f.val k, f.property.1.continuous.comp continuous_subtype_val⟩
  map_add' _ _ := by ext k; rfl
  map_smul' _ _ := by ext k; rfl

theorem restrict_injective (n : ℕ) (ds : List RealBlock) :
    Function.Injective (restrict n ds) := by
  intro f H h
  apply Subtype.ext
  funext g
  obtain ⟨d, u, k, hk, rfl⟩ :=
    exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [f.property.2 d u k, H.property.2 d u k]
  exact congrArg (fun z => principalSeriesCharacter ℝ n (realPositionCharacter ds) d * z)
    (ContinuousMap.congr_fun h ⟨k, hk⟩)

theorem mem_window_restrict_iff {ds : List RealBlock} (hr : realRank ds = n)
    (f : principalSeries ℝ n (realPositionCharacter ds)) :
    restrict n ds f ∈ window n ds ↔ f.val ∈ realStandardModule n ds := by
  simp only [window, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
    ∀ j : ℤ, |j| < |d.weight| → ∀ k : K, blockFourierCoefficient n p j f.val k = 0) ↔ _
  refine ⟨fun h => RealKTypeTransport.mem_realStandardModule_of_unitaryCompact hr f.property
    (fun p d hd j hj k hk => h p d hd j hj ⟨k, hk⟩), ?_⟩
  exact fun h p d hd j hj k => h.2 p d hd j hj k

/-- The topology on the smooth position principal series induced by compact restriction. -/
abbrev compactRestrictionTopology (n : ℕ) (ds : List RealBlock) :
    TopologicalSpace (principalSeries ℝ n (realPositionCharacter ds)) :=
  TopologicalSpace.induced (restrict n ds) inferInstance

/-- Inside the smooth position principal series, the smooth real standard module is
closed for the compact supremum topology. -/
def RealStandardCompactClosedStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    IsClosed[compactRestrictionTopology n ds]
      {f : principalSeries ℝ n (realPositionCharacter ds) | f.val ∈ realStandardModule n ds}

theorem realStandardCompactClosed : RealStandardCompactClosedStatement := by
  intro n ds hr
  have hSet : {f : principalSeries ℝ n (realPositionCharacter ds) |
      f.val ∈ realStandardModule n ds} =
      (restrict n ds) ⁻¹' (window n ds : Set C(unitaryCompact ℝ n, ℂ)) :=
    Set.ext fun f => (mem_window_restrict_iff hr f).symm
  rw [hSet]
  let := compactRestrictionTopology n ds
  exact (isClosed_window n ds).preimage continuous_induced_dom

end Langlands.Archimedean.RealStandardCompactWindow
