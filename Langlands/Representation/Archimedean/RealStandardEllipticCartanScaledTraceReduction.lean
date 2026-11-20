import Langlands.Representation.Archimedean.RealStandardEllipticCartanMatrix
import Langlands.Representation.Archimedean.RealStandardCompactTestTrace
import Langlands.Representation.Archimedean.RealStandardEllipticCartanNumeratorScale

/-! # Elliptic Cartan comparison with a separate constant for each block list -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace Langlands.Archimedean.RealStandardEllipticCartan

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean RealStandardCompactAverage

local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ

/-- The trace limit formula with a nonzero constant for each original list, shared across
its Cartan coordinates and enumerations. -/
def RealStandardEllipticCartanScaledTraceLimitsStatement : Prop :=
  ∃ B : List RealBlock → ℂ, (∀ ds, B ds ≠ 0) ∧
    ∀ (r s : ℕ) (x : Coordinates r s), x ∈ separatedRegularCoordinates r s →
      ∃ (μ : Measure (K (2 * r + s))) (L : Filter C(K (2 * r + s), ℂ)) (c : ℂ),
        μ.IsHaarMeasure ∧ L.NeBot ∧ c ≠ 0 ∧
        (∀ {r' s' : ℕ} {ds : List RealBlock}
          {d : Fin r' → ComplexCharacterData} {b : Fin s' → RealCharacterData},
          realRank ds = 2 * r + s → ds.Perm (ofBlockData d b) →
            (∀ i, 0 < (d i).weight) → r' < r →
            Tendsto (compactTestTrace μ ds (cartanElement rfl x)) L (𝓝 0)) ∧
        (∀ {ds : List RealBlock} {d : Fin r → ComplexCharacterData} {b : Fin s → RealCharacterData},
          realRank ds = 2 * r + s → ds.Perm (ofBlockData d b) →
            (∀ i, 0 < (d i).weight) →
            Tendsto (compactTestTrace μ ds (cartanElement rfl x)) L
              (𝓝 (c * (B ds * numerator (blockParameters d b) x))))

private theorem enumerated_weight_pos {r s : ℕ} {ds : List RealBlock}
    {d : Fin r → ComplexCharacterData} {b : Fin s → RealCharacterData}
    (hp : ds.Perm (ofBlockData d b))
    (hw : ∀ a : ComplexCharacterData, .induced a ∈ ds → 0 < a.weight) (i : Fin r) :
    0 < (d i).weight := by
  apply hw
  exact hp.mem_iff.mpr (List.mem_append_left _ (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)))

/-- The exact comparison follows from trace limits with list-dependent constant factors. -/
theorem realStandardEllipticCartanComparison_of_scaledTraceLimits
    (hlimits : RealStandardEllipticCartanScaledTraceLimitsStatement) :
    RealStandardEllipticCartanComparisonStatement := by
  obtain ⟨B, hB, hlimits⟩ := hlimits
  intro n ds es hn hm hd he _ _ T hT hbij
  obtain ⟨r, s, d, c, hdp⟩ := exists_ofBlockData_perm ds
  obtain ⟨r', s', e, b, hep⟩ := exists_ofBlockData_perm es
  have hdn : 2 * r + s = n := (realRank_ofBlockData d c).symm.trans
    ((hdp.map RealBlock.rank).sum_eq.symm.trans hn)
  have hen : 2 * r' + s' = n := (realRank_ofBlockData e b).symm.trans
    ((hep.map RealBlock.rank).sum_eq.symm.trans hm)
  have hd' := enumerated_weight_pos hdp hd
  have he' := enumerated_weight_pos hep he
  have htrace {u v : ℕ} (hh : 2 * u + v = n) (x : Coordinates u v)
      (μ : Measure (K (2 * u + v))) [μ.IsHaarMeasure] :
      compactTestTrace μ ds (cartanElement rfl x) = compactTestTrace μ es (cartanElement rfl x) := by
    cases hh
    exact realStandardCompactTestTrace (2 * u + v) μ ds es hn hm T hT hbij (cartanElement rfl x)
  have hle : r ≤ r' := by
    by_contra! hlt
    obtain ⟨x, hx, hxnum⟩ := exists_separated_numerator_ne_zero (p := blockParameters d c) hd'
    obtain ⟨μ, L, C, hμ, hL, hC, hbelow, htop⟩ := hlimits r s x hx
    have ht := htop (hn.trans hdn.symm) hdp hd'
    have hz := hbelow (hm.trans hdn.symm) hep he' hlt
    rw [htrace hdn x μ] at ht
    exact (mul_ne_zero hC (mul_ne_zero (hB ds) hxnum)) (tendsto_nhds_unique ht hz)
  have hge : r' ≤ r := by
    by_contra! hlt
    obtain ⟨x, hx, hxnum⟩ := exists_separated_numerator_ne_zero (p := blockParameters e b) he'
    obtain ⟨μ, L, C, hμ, hL, hC, hbelow, htop⟩ := hlimits r' s' x hx
    have ht := htop (hm.trans hen.symm) hep he'
    have hz := hbelow (hn.trans hen.symm) hdp hd' hlt
    rw [htrace hen x μ] at hz
    exact (mul_ne_zero hC (mul_ne_zero (hB es) hxnum)) (tendsto_nhds_unique ht hz)
  have hr : r = r' := le_antisymm hle hge
  subst r'
  have hs : s = s' := by omega
  subst s'
  have hscaled : (fun x => B ds * numerator (blockParameters d c) x) =
      (fun x => B es * numerator (blockParameters e b) x) := by
    apply Continuous.ext_on (dense_separatedRegularCoordinates r s)
      (continuous_const.mul (continuous_numerator _)) (continuous_const.mul (continuous_numerator _))
    intro x hx
    obtain ⟨μ, L, C, hμ, hL, hC, _, htop⟩ := hlimits r s x hx
    have ht := htop (hn.trans hdn.symm) hdp hd'
    have ht' := htop (hm.trans hdn.symm) hep he'
    rw [htrace hdn x μ] at ht
    exact mul_left_cancel₀ hC (tendsto_nhds_unique ht ht')
  refine ⟨r, s, d, e, c, b, hdp, hep, ?_⟩
  exact (scalars_eq_and_numerator_eq_of_mul_eq hd' he' (hB ds) (hB es) (congrFun hscaled)).2

end Langlands.Archimedean.RealStandardEllipticCartan
