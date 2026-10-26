import Langlands.HarmonicAnalysis.CompactOpenAnnihilatorStatement
import Langlands.Representation.Hecke.TestFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Regular

/-! Compactness of compact-open annihilators from scalar Fourier self-duality. -/

noncomputable section

open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace Langlands.HarmonicAnalysis

universe u

/-- For a regular left-invariant measure that is positive on nonempty open sets,
an open additive subgroup of finite measure is compact. -/
theorem isCompact_addSubgroup_of_measure_lt_top {G : Type*} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.Regular]
    [μ.IsOpenPosMeasure] (A : AddSubgroup G) (hAo : IsOpen (A : Set G))
    (hA : μ (A : Set G) < ∞) : IsCompact (A : Set G) := by
  have hpos : μ (A : Set G) ≠ 0 := hAo.measure_ne_zero μ ⟨0, A.zero_mem⟩
  obtain ⟨K, hKA, hKc, hK⟩ := hAo.exists_lt_isCompact (ENNReal.half_lt_self hpos hA.ne)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  refine ((hKc.prod hKc).image continuous_sub).of_isClosed_subset
    (A.isClosed_of_isOpen hAo) ?_
  intro a ha
  by_contra hnot
  have hdisj : Disjoint ((fun x => -a + x) ⁻¹' K) K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    refine hnot ⟨(x, -a + x), ⟨hxK, hx⟩, ?_⟩
    change x - (-a + x) = a
    rw [sub_eq_add_neg, neg_add_rev, neg_neg, add_neg_cancel_left]
  have hsub : (fun x => -a + x) ⁻¹' K ∪ K ⊆ (A : Set G) := by
    refine union_subset (fun x hx => ?_) hKA
    have h : a + (-a + x) ∈ A := A.add_mem ha (hKA hx)
    rwa [add_neg_cancel_left] at h
  have hle := measure_mono (μ := μ) hsub
  rw [measure_union hdisj hKm, measure_preimage_add] at hle
  have hlt : μ (A : Set G) < μ K + μ K := by
    calc
      μ (A : Set G) = μ (A : Set G) / 2 + μ (A : Set G) / 2 := (ENNReal.add_halves _).symm
      _ < μ K + μ K := ENNReal.add_lt_add hK hK
  exact (not_le.mpr hlt) hle

section Annihilator

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
/-- The annihilator of an additive subgroup is the carrier of an additive subgroup. -/
theorem exists_addSubgroup_annihilator (ψ : UnitaryAdditiveCharacter F)
    (H : AddSubgroup F) :
    ∃ A : AddSubgroup F,
      (A : Set F) = {y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1} :=
  ⟨{ carrier := {y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1}
     zero_mem' := fun x _ => by simp
     add_mem' := fun {a b} ha hb x hx => by
       rw [mul_add, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
     neg_mem' := fun {a} ha x hx => by
       rw [mul_neg, ← neg_mul]
       exact ha (-x) (H.neg_mem hx) }, rfl⟩

/-- The annihilator of a compact additive subgroup is a neighborhood of zero. -/
theorem annihilator_mem_nhds_zero (ψ : UnitaryAdditiveCharacter F)
    (H : AddSubgroup F) (hH : IsCompact (H : Set F)) :
    {y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1} ∈ 𝓝 (0 : F) := by
  have harc : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  let U : Set F := ψ.toAddChar ⁻¹' Circle.centeredArc (Real.pi / 2)
  have hU : IsOpen U := (Circle.isOpen_centeredArc _).preimage ψ.continuous_toFun
  have h : ∀ᶠ y in 𝓝 (0 : F), ∀ x ∈ (H : Set F), x * y ∈ U := by
    apply hH.eventually_forall_of_forall_eventually
    intro x _
    have hc : Continuous fun p : F × F => p.2 * p.1 := continuous_snd.mul continuous_fst
    refine hc.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    change ψ.toAddChar (x * 0) ∈ Circle.centeredArc (Real.pi / 2)
    rwa [mul_zero, AddChar.map_zero_eq_one]
  filter_upwards [h] with y hy x hx
  have he : ψ.toAddChar (x * y) = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    have hn := hy (n • x) (H.nsmul_mem hx n)
    change ψ.toAddChar (n • x * y) ∈ Circle.centeredArc (Real.pi / 2) at hn
    rwa [smul_mul_assoc, AddChar.map_nsmul_eq_pow] at hn
  change ((ψ.toAddChar (x * y) : Circle) : ℂ) = 1
  rw [he, Circle.coe_one]

variable [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]

/-- Under self-duality, the annihilator of a compact open additive subgroup has
finite Haar measure. -/
theorem measure_annihilator_lt_top (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (hψμ : IsSelfDual ψ μ) (H : OpenAddSubgroup F)
    (hH : IsCompact (H : Set F)) :
    μ.measure {y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1} < ∞ := by
  let f : SchwartzBruhat F := Hecke.TestFunction.characteristic H.isClopen hH
  have hint : Integrable (fourierIntegral ψ μ f) μ.measure := by
    have h0 := (hψμ f).1 0
    simp only [mul_zero, AddChar.map_zero_eq_one, one_mul] at h0
    exact h0
  have hval : ∀ y : F, (∀ x : F, x ∈ H → ψ.complex (x * y) = 1) →
      fourierIntegral ψ μ f y = (μ.measure.real (H : Set F) : ℂ) := by
    intro y hy
    calc
      fourierIntegral ψ μ f y =
          ∫ x, (H : Set F).indicator (fun _ => (1 : ℂ)) x ∂μ.measure := by
        apply integral_congr_ae
        refine ae_of_all _ fun x => ?_
        change ψ.complex (x * y) * f x = (H : Set F).indicator (fun _ => (1 : ℂ)) x
        rw [Hecke.TestFunction.characteristic_apply]
        by_cases hx : x ∈ H
        · rw [hy x hx, one_mul]
        · rw [Set.indicator_of_notMem (by exact hx), mul_zero]
      _ = (μ.measure.real (H : Set F) : ℂ) := by
        rw [integral_indicator_const _ H.isOpen.measurableSet, Complex.real_smul,
          mul_one]
  have hpos : 0 < μ.measure.real (H : Set F) :=
    ENNReal.toReal_pos (H.isOpen.measure_ne_zero μ.measure ⟨0, H.zero_mem⟩)
      hH.measure_lt_top.ne
  calc
    μ.measure {y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1} ≤
        μ.measure {x | μ.measure.real (H : Set F) ≤ ‖fourierIntegral ψ μ f x‖} := by
      refine measure_mono fun y hy => ?_
      change μ.measure.real (H : Set F) ≤ ‖fourierIntegral ψ μ f y‖
      rw [hval y hy, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    _ < ∞ := hint.measure_norm_ge_lt_top hpos

end Annihilator

/-- Scalar Fourier self-duality forces annihilators of compact open additive
subgroups to be compact. -/
theorem compactOpenAnnihilator : CompactOpenAnnihilatorStatement.{u} := by
  intro F _ _ _ _ _ _ _ _ ψ μ hψμ H hH
  obtain ⟨A, hA⟩ := exists_addSubgroup_annihilator ψ H.toAddSubgroup
  have hAo : IsOpen (A : Set F) := by
    refine A.isOpen_of_mem_nhds (g := 0) ?_
    rw [hA]
    exact annihilator_mem_nhds_zero ψ H.toAddSubgroup hH
  have hAμ : μ.measure (A : Set F) < ∞ := by
    rw [hA]
    exact measure_annihilator_lt_top ψ μ hψμ H hH
  have hAc := isCompact_addSubgroup_of_measure_lt_top μ.measure A hAo hAμ
  rw [hA] at hAc
  exact hAc

end Langlands.HarmonicAnalysis
