import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof
import Langlands.Representation.Hecke.RenardTestDecompositionProof

/-! # Haar distributions in the full algebraic dual -/

noncomputable section

open MeasureTheory
open Langlands.Hecke.TestFunction
open scoped BigOperators

namespace Langlands.HarmonicAnalysis.Distribution.RenardHaar

universe u

open Hecke.RenardTestDecomposition

section AlgebraicUniqueness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem leftInvariant_translate (D : Distribution G) (hD : IsLeftInvariant D)
    (g : G) (f : SchwartzBruhat G) : D (leftTranslate g f) = D f := by
  have h := congrArg (fun E : Distribution G => E f) (hD g⁻¹)
  simpa only [GroupAction.leftDistributions_apply,
    GroupAction.leftTests_eq_leftTranslate, LinearEquiv.coe_coe, inv_inv] using h

theorem leftTranslate_subgroupIndicator (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g x : G) :
    leftTranslate g (subgroupIndicator K hK) x =
      ({y | ∃ k : K, y = g * (k : G)} : Set G).indicator (fun _ => 1) x := by
  classical
  have hm : g⁻¹ * x ∈ K ↔ ∃ k : K, x = g * (k : G) := by
    constructor
    · intro h
      exact ⟨⟨g⁻¹ * x, h⟩, by simp⟩
    · rintro ⟨k, rfl⟩
      simpa only [inv_mul_cancel_left] using k.property
  rw [leftTranslate_apply, subgroupIndicator_apply]
  by_cases hx : g⁻¹ * x ∈ K
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (s := {y | ∃ k : K, y = g * (k : G)}) (hm.mp hx)]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (s := {y | ∃ k : K, y = g * (k : G)}) (mt hm.mpr hx)]

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The coefficient in a coset expansion works for every invariant algebraic
functional simultaneously; no regularity on that functional is needed. -/
theorem invariant_value_of_rightInvariant
    (hexp : RightInvariantExpansionStatement.{u}) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G)
    (hf : ∀ k : K, rightTranslate (k : G) f = f) :
    ∃ a : ℂ, ∀ D : Distribution G, IsLeftInvariant D →
      D f = a * D (subgroupIndicator K hK) := by
  classical
  obtain ⟨n, g, c, -, -, -, heq⟩ := hexp G K hK f hf
  have hfexp : f = ∑ i, c i • leftTranslate (g i) (subgroupIndicator K hK) := by
    ext x
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, leftTranslate_subgroupIndicator] using heq x
  refine ⟨∑ i, c i, fun D hD => ?_⟩
  rw [hfexp, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, leftInvariant_translate D hD]

theorem leftInvariant_scalar_unique
    (hexp : RightInvariantExpansionStatement.{u})
    (T : Distribution G) (hT : IsPositive T) (hTl : IsLeftInvariant T)
    (S : Distribution G) (hSl : IsLeftInvariant S) :
    ∃! c : ℂ, S = c • T := by
  classical
  obtain ⟨K₀, -, hK₀, -⟩ :=
    commonCompactOpenBiInvariance G ∅ ⊤
  let φ₀ := subgroupIndicator K₀ hK₀
  have hφ₀ : φ₀ ≠ 0 := characteristic_ne_zero K₀.isClopen hK₀ ⟨1, K₀.one_mem⟩
  have hφ₀pos := hT φ₀ hφ₀ (characteristic_nonnegative K₀.isClopen hK₀)
  have hTφ₀ : T φ₀ ≠ 0 := by
    intro h
    simpa [h] using hφ₀pos.2
  let c := S φ₀ / T φ₀
  have heq : S = c • T := by
    ext f
    obtain ⟨K, -, hK, hfamily⟩ :=
      commonCompactOpenBiInvariance G {f, φ₀} ⊤
    have hf := (mem_biInvariant_iff _ _ _).mp (hfamily f (by simp))
    have hφ := (mem_biInvariant_iff _ _ _).mp (hfamily φ₀ (by simp))
    obtain ⟨a, ha⟩ := invariant_value_of_rightInvariant hexp K hK φ₀ hφ.2
    obtain ⟨b, hb⟩ := invariant_value_of_rightInvariant hexp K hK f hf.2
    have ha0 : a ≠ 0 := by
      intro hz
      exact hTφ₀ (by rw [ha T hTl, hz, zero_mul])
    have hratio : S (subgroupIndicator K hK) = c * T (subgroupIndicator K hK) := by
      have hreference : a * S (subgroupIndicator K hK) =
          c * (a * T (subgroupIndicator K hK)) := by
        rw [← ha S hSl, ← ha T hTl]
        exact (div_mul_cancel₀ _ hTφ₀).symm
      apply mul_left_cancel₀ ha0
      simpa only [mul_left_comm c a] using hreference
    change S f = c * T f
    rw [hb S hSl, hb T hTl, hratio]
    ring
  refine ⟨c, heq, fun d hd => ?_⟩
  have hvalue := congrArg (fun D : Distribution G => D φ₀) (hd.symm.trans heq)
  change d * T φ₀ = c * T φ₀ at hvalue
  exact mul_right_cancel₀ hTφ₀ hvalue

end AlgebraicUniqueness

theorem measureHaarBridge_of_expansion (hexp : RightInvariantExpansionStatement.{u}) :
    MeasureHaarBridgeStatement.{u} := by
  intro G _ _ _ _ _ _ _ _ μ _
  exact ⟨ofMeasure_positive μ, ofMeasure_leftInvariant μ,
    fun T hT => leftInvariant_scalar_unique hexp (ofMeasure μ)
      (ofMeasure_positive μ) (ofMeasure_leftInvariant μ) T hT⟩

theorem leftHaar_of_expansion (hexp : RightInvariantExpansionStatement.{u}) :
    LeftHaarStatement.{u} := by
  intro G _ _ _ _ _ _
  let _ : MeasurableSpace G := borel G
  let _ : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  exact ⟨ofMeasure μ, measureHaarBridge_of_expansion hexp G μ⟩

/-- Actual Haar integration classifies every left-invariant algebraic distribution. -/
theorem measureHaarBridge : MeasureHaarBridgeStatement.{u} :=
  measureHaarBridge_of_expansion rightInvariantExpansion

/-- Positive left Haar distributions exist and are unique up to a complex scalar. -/
theorem leftHaar : LeftHaarStatement.{u} :=
  leftHaar_of_expansion rightInvariantExpansion

end Langlands.HarmonicAnalysis.Distribution.RenardHaar
