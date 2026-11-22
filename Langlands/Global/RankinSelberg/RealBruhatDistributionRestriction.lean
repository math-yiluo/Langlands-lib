import Langlands.Global.RankinSelberg.RealBruhatChartVanishing
import Langlands.Group.GL.RealBruhatChartRank
import Langlands.HarmonicAnalysis.Distribution.OpenTestChartTransport

/-! # A real Whittaker distribution is determined on the open Bruhat cell -/

noncomputable section

open Set TopologicalSpace
open Langlands.GeneralLinear Langlands.GeneralLinear.RealBruhatProductChart
open Langlands.GeneralLinear.RealBruhatChartRank Langlands.HarmonicAnalysis
open scoped ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBruhatDistributionRestriction

open RealBruhatChartVanishing

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ

/-- The open domain of invertible real matrices for the distribution tests. -/
def invertibleDomain (r : ℕ) : Opens (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :=
  ⟨range (Units.val : Langlands.GeneralLinear (r + 1) ℝ → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
    Units.isOpenEmbedding_val.isOpen_range⟩

/-- Ambient left infinitesimal upper-unipotent invariance and right
Whittaker covariance, with eigenvalue `eigen` in adjacent right directions. -/
def IsInfinitesimalWhittakerCovariant (D : 𝓓'(invertibleDomain r, ℂ)) (eigen : ℂ) : Prop :=
  ∀ j (f : 𝓓(invertibleDomain r, ℝ)),
    D (smoothVectorFieldDerivativeTest (ambientField j).contDiff.contDiffOn f) =
      eigen * (characterWeight j • D f)

/-- The reversal Bruhat cell viewed as a set of real matrices. -/
def reversalCellImage (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :=
  Units.val '' upperBruhatCell (r + 1) ℝ Fin.revPerm

theorem chart_target_subset_invertibleDomain (w : Equiv.Perm (Fin (r + 1))) :
    (productChart w).target ⊆ invertibleDomain r := by
  intro y hy
  have h := isUnit_of_mem_productChart_target w hy
  exact ⟨h.unit, IsUnit.unit_spec _⟩

theorem reversal_chart_target_eq :
    (productChart (Fin.revPerm : Equiv.Perm (Fin (r + 1)))).target = reversalCellImage r := by
  apply subset_antisymm
  · intro y hy
    obtain ⟨g, hg⟩ := chart_target_subset_invertibleDomain Fin.revPerm hy
    have hgt : g.val ∈ (productChart Fin.revPerm).target := hg.symm ▸ hy
    refine ⟨g, (mem_cell_iff_normal_eq_zero _ hgt).mpr ?_, hg⟩
    funext ij
    have h := ij.property.2
    simp only [Equiv.Perm.inv_def, Fin.revPerm_symm, Fin.revPerm_apply] at h
    exact False.elim ((not_lt_of_gt ij.property.1) (Fin.rev_lt_rev.mp h))
  · rintro y ⟨g, hg, rfl⟩
    exact mem_productChart_target_of_mem_cell Fin.revPerm hg

private theorem isChartWhittakerCovariant (w : Equiv.Perm (Fin (r + 1)))
    (D : 𝓓'(invertibleDomain r, ℂ)) (eigen : ℂ) (hD : IsInfinitesimalWhittakerCovariant D eigen) :
    IsChartWhittakerCovariant w
      (chartOpenDistribution (productChart w) (contDiffOn_productChart_symm w)
        (chart_target_subset_invertibleDomain w) D) eigen := by
  intro j f
  let e := productChart w
  let hΩ := chart_target_subset_invertibleDomain w
  let hei := contDiffOn_productChart_symm w
  change D (chartTestToOpenCLM e hei hΩ
    (smoothVectorFieldDerivativeTest (contDiffOn_coordinateField w j) f)) =
    eigen * (characterWeight j • D (chartTestToOpenCLM e hei hΩ f))
  rw [chartTestToOpenCLM_smoothVectorFieldDerivativeTest _ _ _
    (ambientField j).contDiff (contDiffOn_coordinateField w j)]
  exact hD j _

/-- Under left infinitesimal invariance and nonzero right Whittaker covariance,
vanishing on tests supported in the reversal Bruhat cell implies vanishing. -/
theorem eq_zero_of_reversalCell_vanishing (D : 𝓓'(invertibleDomain r, ℂ)) (eigen : ℂ)
    (heigen : eigen ≠ 0) (hD : IsInfinitesimalWhittakerCovariant D eigen)
    (hrev : Distribution.IsVanishingOn D (reversalCellImage r)) : D = 0 := by
  let length (v : Equiv.Perm (Fin (r + 1))) := permutationInversionCount (r + 1) v
  let bound := (r + 1) * (r + 1)
  have hbound (v : Equiv.Perm (Fin (r + 1))) : length v ≤ bound := by
    change permutationInversionCount (r + 1) v ≤ (r + 1) * (r + 1)
    rw [permutationInversionCount_eq_card]
    simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1)))
      (fun p => p.1 < p.2 ∧ v p.2 < v p.1))
  have hcharts (k : ℕ) :
      ∀ w : Equiv.Perm (Fin (r + 1)), bound - length w = k →
        Distribution.IsVanishingOn D (productChart w).target := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hk
      by_cases hw : w = Fin.revPerm
      · subst w
        rwa [reversal_chart_target_eq]
      let H := {v : Equiv.Perm (Fin (r + 1)) // length w < length v}
      let s (j : H) : Set M := (productChart j.val).target
      have hs (j : H) : Distribution.IsVanishingOn D (s j) := by
        have hj := j.property
        have hb := hbound j.val
        exact ih (bound - length j.val) (by omega) j.val rfl
      have hhigh := smoothDistribution_isVanishingOn_iUnion D s
        (fun j => (productChart j.val).open_target) hs
      let e := productChart w
      let he := contDiffOn_productChart w
      let hei := contDiffOn_productChart_symm w
      let hΩ := chart_target_subset_invertibleDomain w
      let T := chartOpenDistribution e hei hΩ D
      have hoff : Distribution.IsVanishingOn T {z : Tangent w × Normal w | z.2 ≠ 0} := by
        apply isVanishingOn_chartOpenDistribution e hei hΩ D hhigh
        rintro y ⟨z, ⟨hz, hzS⟩, rfl⟩
        have hy := e.map_source hzS
        obtain ⟨g, hg⟩ := hΩ hy
        have hgt : g.val ∈ e.target := hg.symm ▸ hy
        have hgC : g ∉ upperBruhatCell (r + 1) ℝ w := by
          intro hc
          have hn := (mem_cell_iff_normal_eq_zero w hgt).mp hc
          rw [hg, e.left_inv hzS] at hn
          exact hz hn
        rcases mem_cellNeighborhood_of_mem_productChart_target w g hgt with hc | ⟨v, hv, hcv⟩
        · exact (hgC hc).elim
        · exact mem_iUnion.mpr ⟨⟨v, hv⟩, hg ▸ mem_productChart_target_of_mem_cell v hcv⟩
      have hzero : T = 0 := chartDistribution_eq_zero_of_covariance w hw T hoff
        eigen heigen (isChartWhittakerCovariant w D eigen hD)
      exact isVanishingOn_target_of_chartOpenDistribution_eq_zero e hei he hΩ D hzero
  have hcover : (invertibleDomain r : Set M) ⊆ ⋃ w : Equiv.Perm (Fin (r + 1)), (productChart w).target := by
    rintro y ⟨g, rfl⟩
    obtain ⟨w, hw⟩ := exists_mem_upperBruhatCell g
    exact mem_iUnion.mpr ⟨w, mem_productChart_target_of_mem_cell w hw⟩
  have hv := smoothDistribution_isVanishingOn_iUnion D (fun w => (productChart w).target)
    (fun w => (productChart w).open_target) (fun w => hcharts _ w rfl)
  apply DFunLike.ext
  intro f
  exact hv f (f.tsupport_subset.trans hcover)

/-- With left infinitesimal invariance and nonzero right Whittaker covariance,
the restriction to the reversal Bruhat cell determines the distribution. -/
def RealBruhatDistributionRestrictionStatement : Prop :=
  ∀ (r : ℕ) (D : 𝓓'(invertibleDomain r, ℂ)) (eigen : ℂ), eigen ≠ 0 →
    IsInfinitesimalWhittakerCovariant D eigen →
    Distribution.IsVanishingOn D (reversalCellImage r) → D = 0

theorem realBruhatDistributionRestriction : RealBruhatDistributionRestrictionStatement :=
  fun _ => eq_zero_of_reversalCell_vanishing

end Langlands.Global.RankinSelbergGlobal.RealBruhatDistributionRestriction
