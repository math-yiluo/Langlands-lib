import Langlands.Representation.Whittaker.ModelKirillovStatement
import Langlands.Group.GL.Mirabolic
import Langlands.Analysis.Local.QuotientTopology

/-!
# Compatibility of compact mirabolic test data

The prescribed support and right invariance of compact mirabolic test data
give the existing Kirillov test-function predicate. Opposite prescribed
character values give the indicator of the actual quotient image.
-/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis RankinSelberg QuotientIntegration

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- The image of a specified mirabolic subgroup in the actual left-unipotent
quotient. The subgroup is not assumed compact or open. -/
def mirabolicQuotientSupport
    (K : Subgroup (GeneralLinear.mirabolic n F)) :
    Set (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)) :=
  leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) ''
    ((fun k : GeneralLinear.mirabolic n F => k.val) '' (K : Set _))

/-- Compact mirabolic support and a right stabilizer containing an ambient
open subgroup's mirabolic intersection give the shared test-function predicate.
The assumptions are concrete conditions on the specified function. -/
theorem isMirabolicTestFunction_of_compact_mirabolic_support
    (ψ : UnitaryAdditiveCharacter F) (φ : WhittakerFunctions ψ n)
    (K : Subgroup (GeneralLinear.mirabolic n F))
    (hK : IsCompact (K : Set (GeneralLinear.mirabolic n F)))
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hJ : ∀ j : Langlands.GeneralLinear (n + 1) F,
      j ∈ J → j ∈ GeneralLinear.mirabolic n F →
        j ∈ (fun k : GeneralLinear.mirabolic n F => k.val) '' (K : Set _))
    (hzero : ∀ g : Langlands.GeneralLinear (n + 1) F,
      g ∉ {g | ∃ u : GeneralLinear.upperUnipotent (n + 1) F,
        ∃ k : K, g = u.val * k.val.val} → φ.val g = 0)
    (hright : ∀ (g : Langlands.GeneralLinear (n + 1) F) (k : K),
      φ.val (g * k.val.val) = φ.val g) :
    IsMirabolicTestFunction ψ n φ := by
  constructor
  · refine ⟨J, ?_⟩
    intro q k _hq hk hkJ
    obtain ⟨a, ha, hak⟩ := hJ k hkJ hk
    rw [← hak]
    exact hright q ⟨a, ha⟩
  · refine ⟨(fun k : GeneralLinear.mirabolic n F => k.val) '' (K : Set _),
      hK.image continuous_subtype_val, ?_⟩
    intro q _hq hq
    have hsupport : q ∈ {g | ∃ u : GeneralLinear.upperUnipotent (n + 1) F,
        ∃ k : K, g = u.val * k.val.val} := by
      by_contra h
      exact hq (hzero q h)
    obtain ⟨u, k, hqk⟩ := hsupport
    exact ⟨u, k.val.val, ⟨k.val, k.property, rfl⟩, hqk⟩

/-- Opposite character values on `N K`, extended by zero, multiply to the
indicator of the image of `K` in the existing left-unipotent quotient.
This holds at every ambient matrix, including those outside the mirabolic group. -/
theorem mirabolicTests_product_eq_quotient_indicator
    (ψ : UnitaryAdditiveCharacter F)
    (φ : WhittakerFunctions ψ n) (φ' : InverseWhittakerFunctions ψ n)
    (K : Subgroup (GeneralLinear.mirabolic n F))
    (hvalues : ∀ (u : GeneralLinear.upperUnipotent (n + 1) F) (k : K),
      φ.val (u.val * k.val.val) = (standardCharacter ψ n u : ℂ) ∧
      φ'.val (u.val * k.val.val) = (standardCharacter ψ n u : ℂ)⁻¹)
    (hzero : ∀ g : Langlands.GeneralLinear (n + 1) F,
      g ∉ {g | ∃ u : GeneralLinear.upperUnipotent (n + 1) F,
        ∃ k : K, g = u.val * k.val.val} →
      φ.val g = 0 ∧ φ'.val g = 0)
    (g : Langlands.GeneralLinear (n + 1) F) :
    φ.val g * φ'.val g =
      (mirabolicQuotientSupport K).indicator
        (fun _ => (1 : ℂ))
        (leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) g) := by
  classical
  by_cases hg : leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) F) g ∈
      mirabolicQuotientSupport K
  · rw [Set.indicator_of_mem hg]
    obtain ⟨_, ⟨k, hk, rfl⟩, hkg⟩ := hg
    have hu : g * k.val⁻¹ ∈ GeneralLinear.upperUnipotent (n + 1) F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hkg)
    let u : GeneralLinear.upperUnipotent (n + 1) F := ⟨g * k.val⁻¹, hu⟩
    have hfactor : g = u.val * k.val := by simp [u]
    rw [hfactor, (hvalues u ⟨k, hk⟩).1, (hvalues u ⟨k, hk⟩).2]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  · rw [Set.indicator_of_notMem hg]
    have hsupport : g ∉ {g | ∃ u : GeneralLinear.upperUnipotent (n + 1) F,
        ∃ k : K, g = u.val * k.val.val} := by
      rintro ⟨u, k, hgk⟩
      apply hg
      refine ⟨k.val.val, ⟨k.val, k.property, rfl⟩, ?_⟩
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      rw [hgk]
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using u.property
    rw [(hzero g hsupport).1, zero_mul]

end Langlands.Whittaker
