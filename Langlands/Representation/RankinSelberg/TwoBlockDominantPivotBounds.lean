import Langlands.Representation.RankinSelberg.TwoBlockDominantPivot
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport

/-! # Opposing Iwasawa bounds about the dominant singleton -/

noncomputable section

open scoped BigOperators

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockLowerFixedSlice TwoBlockConvergence
  TwoBlockDeformation

universe uF uV

/-- Adjacent root support normalized at an isolated unit coordinate, with the
resulting opposing cone on all diagonal exponents. -/
def PivotCone {r : ℕ} (L : ℕ) (i : Fin (r + 1))
    (lam : Fin (r + 1) → ℤ) : Prop :=
  RootBounded L lam ∧ lam i = 0 ∧
    OppositeCone (r * L) (Finset.Iic i) lam

/-- A normalized coordinate and adjacent root bounds give an opposing cone on
the entire diagonal lattice. -/
theorem oppositeCone_of_pivot {r L : ℕ} {lam : Fin (r + 1) → ℤ}
    (hroot : RootBounded L lam) (i : Fin (r + 1)) (hpivot : lam i = 0) :
    OppositeCone (r * L) (Finset.Iic i) lam := by
  constructor
  · intro l hl
    have h := hroot.le_of_le (Finset.mem_Iic.mp hl)
    rw [hpivot] at h
    push_cast
    linarith
  · intro l hl
    have hil : i ≤ l := le_of_not_ge fun hle => hl (Finset.mem_Iic.mpr hle)
    have h := hroot.le_of_le hil
    rw [hpivot] at h
    simpa using h

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The isolated unit fixes the integer exponent at the pivot in every
canonical Iwasawa decomposition. -/
theorem torusExponent_pivot {r : ℕ}
    (M u : GeneralLinear (r + 1) F.Carrier) (lam : Fin (r + 1) → ℤ)
    (κ : GeneralLinear (r + 1) F.Carrier) (i c : Fin (r + 1))
    (hp : IsUnitPivot M i c) (hu : u ∈ upperUnipotent (r + 1) F.Carrier)
    (hκ : κ ∈ integralOpen F r)
    (he : M = u * Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * κ) :
    lam i = 0 := by
  have hκ' : κ ∈ Conductor.integralSubgroup
      (ValuativeRel.valuation F.Carrier).integer r :=
    (Conductor.mem_integralSubgroup _ _ κ).mpr ((mem_integralOpen F κ).mp hκ)
  have ha := normalizedAbs_diagonal_pivot F F.canonicalTopologicalData M u
    (fun l => LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData ^ lam l)
    κ i c hp hu hκ' he
  rw [normalizedAbs_uniformizer_zpow F] at ha
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hexp : -(lam i) = (0 : ℤ) := by
    apply (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq))
    simpa only [zpow_zero] using ha
  omega

/-- One integer root bound, chosen before every matrix and pivot, controls all
Iwasawa exponents of a nonzero actual smooth coefficient at an isolated unit. -/
theorem exists_coefficient_pivot_cone (ψ : UnitaryAdditiveCharacter F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ L : ℕ, ∀ (M u : GeneralLinear (r + 1) F.Carrier)
      (lam : Fin (r + 1) → ℤ) (κ : GeneralLinear (r + 1) F.Carrier)
      (i c : Fin (r + 1)),
      IsUnitPivot M i c →
      W.val.val M ≠ 0 →
      u ∈ upperUnipotent (r + 1) F.Carrier →
      κ ∈ integralOpen F r →
      M = u * Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * κ →
      PivotCone L i lam := by
  obtain ⟨L, hL⟩ := exists_coefficient_rootBounded F ψ π hπ ell W
  refine ⟨L, fun M u lam κ i c hp hW hu hκ he => ?_⟩
  have hW' : W.val.val (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * κ) ≠ 0 := by
    intro hz
    apply hW
    rw [he, mul_assoc, W.val.property ⟨u, hu⟩, hz, mul_zero]
  have hroot := hL lam κ hκ hW'
  have hzero := torusExponent_pivot F M u lam κ i c hp hu hκ he
  exact ⟨hroot, hzero, oppositeCone_of_pivot hroot i hzero⟩

/-- Uniform Iwasawa support about the separating singleton for the actual
strict-dominant matrix, with every complementary rectangle size retained. -/
theorem exists_matrix_pivot_cone (ψ : UnitaryAdditiveCharacter F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ L : ℕ, ∀ {t j k : ℕ} {m : Fin 2 → ℕ}
      (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
      (g : GeneralLinear (t + 1) F.Carrier)
      (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
      (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
      W.val.val (matrix h hr g x y) ≠ 0 →
      ∃ u ∈ upperUnipotent (r + 1) F.Carrier,
        ∃ lam : Fin (r + 1) → ℤ, ∃ κ ∈ integralOpen F r,
          matrix h hr g x y = u * Iwasawa.torus
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * κ ∧
          PivotCone L (pivotRow h hr) lam := by
  obtain ⟨L, hL⟩ := exists_coefficient_pivot_cone F ψ π hπ ell W
  refine ⟨L, fun h hr g x y hW => ?_⟩
  obtain ⟨u, hu, lam, κ, hκ, he⟩ :=
    Iwasawa.exists_iwasawa (uniformizerUnit_isUniformizingElement F) (matrix h hr g x y)
  have hκ' : κ ∈ integralOpen F r :=
    (mem_integralOpen F κ).mpr ((Conductor.mem_integralSubgroup _ _ κ).mp hκ)
  exact ⟨u, hu, lam, κ, hκ', he,
    hL _ _ _ _ _ _ (isUnitPivot_matrix h hr g x y) hW hu hκ' he⟩

end Langlands.RankinSelberg.TwoBlockDominantRectangular
