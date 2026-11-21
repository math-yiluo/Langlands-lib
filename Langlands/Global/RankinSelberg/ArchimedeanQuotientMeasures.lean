import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Analysis.Local.ModularCharacterContinuity
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Representation.Unitary.CentralQuotientForm
import Mathlib.Analysis.RCLike.Lemmas

/-! # Compatible quotient measures for the archimedean Rankin–Selberg integrals -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

open Langlands.GeneralLinear.UpperUnipotent (entry_diag entry_eq_zero)
open RankinSelberg (LeftUnipotentQuotient)

variable {K : Type} [RCLike K] {n : ℕ}

private def scaleEntries (z : K) (u : Langlands.GeneralLinear.upperUnipotent n K) : Matrix (Fin n) (Fin n) K :=
  fun i j => z ^ ((j : ℕ) - (i : ℕ)) * u.val.val i j

private theorem scaleEntries_triangular (z : K) (u : Langlands.GeneralLinear.upperUnipotent n K) :
    (scaleEntries z u).IsUpperTriangular := by
  intro i j h
  change j < i at h
  change z ^ ((j : ℕ) - (i : ℕ)) * u.val i j = 0
  rw [entry_eq_zero u h, mul_zero]

private theorem scaleEntries_diagonal (z : K) (u : Langlands.GeneralLinear.upperUnipotent n K) (i : Fin n) :
    scaleEntries z u i i = 1 := by
  simp [scaleEntries]

private def scaleUnipotent (z : K) (u : Langlands.GeneralLinear.upperUnipotent n K) : Langlands.GeneralLinear.upperUnipotent n K :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (scaleEntries z u) (by
    rw [Matrix.det_of_isUpperTriangular (scaleEntries_triangular z u)]
    rw [Finset.prod_eq_one fun i _ => scaleEntries_diagonal z u i]
    exact one_ne_zero),
    ⟨scaleEntries_triangular z u, scaleEntries_diagonal z u⟩⟩

private theorem scaleUnipotent_mul (z : K) (u v : Langlands.GeneralLinear.upperUnipotent n K) :
    scaleUnipotent z (u * v) = scaleUnipotent z u * scaleUnipotent z v := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change z ^ ((j : ℕ) - (i : ℕ)) * (u.val.val * v.val.val) i j =
    (scaleEntries z u * scaleEntries z v) i j
  rw [Matrix.mul_apply, Finset.mul_sum, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i ≤ k
  · by_cases hkj : k ≤ j
    · have he : (k : ℕ) - (i : ℕ) + ((j : ℕ) - (k : ℕ)) = (j : ℕ) - (i : ℕ) := by omega
      simp only [scaleEntries, ← he, pow_add]
      ring
    · simp [scaleEntries, entry_eq_zero v (lt_of_not_ge hkj)]
  · simp [scaleEntries, entry_eq_zero u (lt_of_not_ge hik)]

private theorem scaleUnipotent_mul_scale (z w : K) (u : Langlands.GeneralLinear.upperUnipotent n K) :
    scaleUnipotent z (scaleUnipotent w u) = scaleUnipotent (z * w) u := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change z ^ ((j : ℕ) - (i : ℕ)) * (w ^ ((j : ℕ) - (i : ℕ)) * u.val.val i j) = _
  rw [← mul_assoc, ← mul_pow]
  rfl

private theorem scaleUnipotent_one (u : Langlands.GeneralLinear.upperUnipotent n K) : scaleUnipotent 1 u = u := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [scaleUnipotent, scaleEntries]

private theorem scaleUnipotent_zero (u : Langlands.GeneralLinear.upperUnipotent n K) : scaleUnipotent 0 u = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change scaleEntries 0 u i j = (1 : Matrix (Fin n) (Fin n) K) i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [scaleEntries, zero_pow (by omega : (j : ℕ) - (i : ℕ) ≠ 0), zero_mul,
      Matrix.one_apply_ne h.ne]
  · rw [scaleEntries_diagonal, Matrix.one_apply_eq]
  · rw [scaleEntries, entry_eq_zero u h, mul_zero, Matrix.one_apply_ne h.ne']

private theorem continuous_scaleUnipotent (z : K) :
    Continuous (scaleUnipotent (n := n) z) := by
  have he : Topology.IsEmbedding (Units.val : (Matrix (Fin n) (Fin n) K)ˣ → Matrix (Fin n) (Fin n) K) :=
    (Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) K)).isEmbedding
  have hc : Continuous (fun u : Langlands.GeneralLinear.upperUnipotent n K => (scaleUnipotent z u).val) := by
    apply he.continuous_iff.mpr
    change Continuous (fun u : Langlands.GeneralLinear.upperUnipotent n K => scaleEntries z u)
    exact continuous_matrix fun i j => continuous_const.mul
      ((continuous_apply_apply i j).comp (he.continuous.comp continuous_subtype_val))
  exact Continuous.subtype_mk hc _

private theorem continuous_scaleUnipotent_parameter (u : Langlands.GeneralLinear.upperUnipotent n K) :
    Continuous (fun z : K => scaleUnipotent z u) := by
  have he : Topology.IsEmbedding (Units.val : (Matrix (Fin n) (Fin n) K)ˣ → Matrix (Fin n) (Fin n) K) :=
    (Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) K)).isEmbedding
  have hc : Continuous (fun z : K => (scaleUnipotent z u).val) := by
    apply he.continuous_iff.mpr
    change Continuous (fun z : K => scaleEntries z u)
    exact continuous_matrix fun i j => (continuous_id.pow _).mul continuous_const
  exact Continuous.subtype_mk hc _

private def scaleUnipotentEquiv (z : Kˣ) : Langlands.GeneralLinear.upperUnipotent n K ≃ₜ* Langlands.GeneralLinear.upperUnipotent n K where
  toFun := scaleUnipotent z.val
  invFun := scaleUnipotent (z⁻¹).val
  left_inv u := by
    rw [scaleUnipotent_mul_scale, ← Units.val_mul, inv_mul_cancel, Units.val_one, scaleUnipotent_one]
  right_inv u := by
    rw [scaleUnipotent_mul_scale, ← Units.val_mul, mul_inv_cancel, Units.val_one, scaleUnipotent_one]
  map_mul' := scaleUnipotent_mul z.val
  continuous_toFun := continuous_scaleUnipotent _
  continuous_invFun := continuous_scaleUnipotent _

variable (K) (t : ℕ)

local instance archimedeanQuotientMatrixLocallyCompact : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) K) :=
  inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → K))
local instance archimedeanQuotientGroupLocallyCompact : LocallyCompactSpace (Langlands.GeneralLinear (t + 1) K) :=
  inferInstanceAs (LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) K)ˣ)
local instance archimedeanQuotientUnipotentLocallyCompact : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K) :=
  (Langlands.GeneralLinear.UpperUnipotent.isClosed (R := K)).locallyCompactSpace
local instance archimedeanQuotientGroupMeasurable : MeasurableSpace (Langlands.GeneralLinear (t + 1) K) := borel _
local instance archimedeanQuotientGroupBorel : BorelSpace (Langlands.GeneralLinear (t + 1) K) := ⟨rfl⟩
local instance archimedeanQuotientUnipotentMeasurable : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K) := borel _
local instance archimedeanQuotientUnipotentBorel : BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K) := ⟨rfl⟩
local instance archimedeanQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient t K) := borel _
local instance archimedeanQuotientBorel : BorelSpace (LeftUnipotentQuotient t K) := ⟨rfl⟩

/-- A nonzero rescaling of the strictly upper entries is an automorphism. Its limit at
zero contracts the group to the identity, so the modular character is trivial. -/
theorem upperUnipotent_modularCharacter_eq_one (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K) :
    modularCharacter u = 1 := by
  let z : K := ((1 / 2 : ℝ) : K)
  have hn : ‖z‖ < 1 := by dsimp [z]; rw [RCLike.norm_ofReal]; norm_num
  have hz : z ≠ 0 := by dsimp [z]; exact RCLike.ofReal_ne_zero.mpr (by norm_num)
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn
  have hcont := Haar.continuous_modularCharacter_of_locallyCompact.comp
    (continuous_scaleUnipotent_parameter u)
  have hlim := (hcont.tendsto (0 : K)).comp hpow
  change Tendsto (fun m : ℕ => modularCharacter (scaleUnipotent (z ^ m) u)) atTop
    (𝓝 (modularCharacter (scaleUnipotent 0 u))) at hlim
  have he (m : ℕ) : modularCharacter (scaleUnipotent (z ^ m) u) = modularCharacter u :=
    Aubert.General.modularCharacter_continuousMulEquiv (scaleUnipotentEquiv (Units.mk0 (z ^ m) (pow_ne_zero m hz))) u
  simp only [he, scaleUnipotent_zero, map_one] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- Compatible quotient measure data exist at every real or complex place in each rank. -/
def archimedeanQuotientMeasureData : QuotientMeasureData t K := by
  let μG : Measure (Langlands.GeneralLinear (t + 1) K) := haar
  let μN : Measure (Langlands.GeneralLinear.upperUnipotent (t + 1) K) := haar
  have hG (a : Kˣ) : modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin (t + 1)) a) = 1 := by
    rw [show modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin (t + 1)) a) =
      haarScalarFactor (μG.map (· * Matrix.GeneralLinearGroup.scalar (Fin (t + 1)) a)) μG from
        modularCharacterFun_eq_haarScalarFactor μG _]
    have he : (fun g : Langlands.GeneralLinear (t + 1) K => g * Matrix.GeneralLinearGroup.scalar _ a) =
        (fun g : Langlands.GeneralLinear (t + 1) K => Matrix.GeneralLinearGroup.scalar _ a * g) :=
      funext fun g => (Matrix.GeneralLinearGroup.scalar_commute a g).symm
    have hmap : μG.map (fun g => g * Matrix.GeneralLinearGroup.scalar _ a) = μG := by
      rw [he, map_mul_left_eq_self]
    have hf (ν : Measure (Langlands.GeneralLinear (t + 1) K)) [ν.IsHaarMeasure] (hν : ν = μG) :
        haarScalarFactor ν μG = 1 := by
      subst ν
      exact haarScalarFactor_self μG
    exact hf _ hmap
  let : μG.IsMulRightInvariant := Haar.isMulRightInvariant_of_modularCharacter_eq_one
    (RankinSelberg.GeneralLinearUnimodularity.character_eq_one modularCharacter hG) μG
  let : μN.IsMulRightInvariant := Haar.isMulRightInvariant_of_modularCharacter_eq_one
    (upperUnipotent_modularCharacter_eq_one K t) μN
  let h := QuotientIntegration.compatibleMeasureExists (Langlands.GeneralLinear.upperUnipotent (t + 1) K)
    (Langlands.GeneralLinear.UpperUnipotent.isClosed (R := K)) μG μN
  exact ⟨μG, inferInstance, μN, inferInstance, inferInstance, h.choose, h.choose_spec⟩

/-- The quotient measure data for the real local integral API. -/
def realQuotientMeasureData (t : ℕ) : RealQuotientMeasureData t :=
  archimedeanQuotientMeasureData ℝ t

/-- The quotient measure data for the complex local integral API. -/
def complexQuotientMeasureData (t : ℕ) : ComplexQuotientMeasureData t :=
  archimedeanQuotientMeasureData ℂ t

end Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
