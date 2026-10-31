import Langlands.Representation.Induction.CompactLocalSectionSpanningProof
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Hecke.TestFunction
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof

/-! Compactly supported group tests generating compact covariant functions. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Induction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [IsHaarMeasure μH] [IsMulRightInvariant μH]
  (χ : H →* ℂˣ) (hχ : Continuous χ)

/-- The actual character-weighted subgroup integral on group tests. -/
def characterOrbitIntegral (φ : SchwartzBruhat G) (g : G) : ℂ :=
  ∫ h : H, ((χ h)⁻¹ : ℂˣ) * φ ((h : G) * g) ∂μH

omit [T2Space G] [IsMulRightInvariant μH] in
include hH hχ in
/-- Closedness of the subgroup and compact support give absolute convergence. -/
theorem characterOrbitIntegrable (φ : SchwartzBruhat G) (g : G) :
    Integrable (fun h : H => (((χ h)⁻¹ : ℂˣ) : ℂ) * φ ((h : G) * g)) μH := by
  have he : Topology.IsClosedEmbedding (fun h : H => (h : G) * g) :=
    (Homeomorph.mulRight g).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
  have hc : HasCompactSupport (fun h : H => φ ((h : G) * g)) :=
    φ.hasCompactSupport.comp_isClosedEmbedding he
  exact ((Units.continuous_val.comp (continuous_inv.comp hχ)).mul
    (φ.continuous.comp (continuous_subtype_val.mul_const g))).integrable_of_hasCompactSupport
      hc.mul_left

omit [T2Space G] [IsHaarMeasure μH] in
/-- Right Haar invariance gives the actual left character covariance. -/
theorem characterOrbitIntegral_left (φ : SchwartzBruhat G) (p : H) (g : G) :
    characterOrbitIntegral H μH χ φ ((p : G) * g) =
      (χ p : ℂ) * characterOrbitIntegral H μH χ φ g := by
  have he (h : H) :
      (((χ h)⁻¹ : ℂˣ) : ℂ) * φ ((h : G) * ((p : G) * g)) =
        (χ p : ℂ) *
          ((((χ (h * p))⁻¹ : ℂˣ) : ℂ) * φ (((h * p : H) : G) * g)) := by
    have hc : (χ p : ℂ) * (((χ p)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [map_mul, mul_inv_rev, Units.val_mul, Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (χ p : ℂ) (((χ p)⁻¹ : ℂˣ) : ℂ), hc, one_mul]
  simp only [characterOrbitIntegral, he, integral_const_mul]
  exact congrArg ((χ p : ℂ) * ·)
    (integral_mul_right_eq_self
      (fun h : H => (((χ h)⁻¹ : ℂˣ) : ℂ) * φ ((h : G) * g)) p)

omit [T2Space G] [IsMulRightInvariant μH] in
include hH hχ in
/-- The character average is additive on actual Schwartz group tests. -/
theorem characterOrbitIntegral_add (φ ψ : SchwartzBruhat G) (g : G) :
    characterOrbitIntegral H μH χ (φ + ψ) g =
      characterOrbitIntegral H μH χ φ g + characterOrbitIntegral H μH χ ψ g := by
  change (∫ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) * (φ ((h : G) * g) + ψ ((h : G) * g)) ∂μH) = _
  simp_rw [mul_add]
  exact integral_add (characterOrbitIntegrable H hH μH χ hχ φ g)
    (characterOrbitIntegrable H hH μH χ hχ ψ g)

omit [IsTopologicalGroup G] [T2Space G]
  [BorelSpace H] [IsHaarMeasure μH] [IsMulRightInvariant μH] in
/-- Scalar multiplication commutes with the total subgroup integral. -/
theorem characterOrbitIntegral_smul (c : ℂ) (φ : SchwartzBruhat G) (g : G) :
    characterOrbitIntegral H μH χ (c • φ) g =
      c * characterOrbitIntegral H μH χ φ g := by
  change (∫ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) * (c * φ ((h : G) * g)) ∂μH) = _
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul _ _

omit [T2Space G] [BorelSpace H]
  [IsHaarMeasure μH] [IsMulRightInvariant μH] in
/-- Right translation of the group test translates its character average. -/
theorem characterOrbitIntegral_translate (φ : SchwartzBruhat G) (a g : G) :
    characterOrbitIntegral H μH χ (Hecke.TestFunction.rightTranslate a φ) g =
      characterOrbitIntegral H μH χ φ (g * a) := by
  simp only [characterOrbitIntegral, Hecke.TestFunction.rightTranslate_apply, mul_assoc]

omit [T2Space G] in
include hH in
private theorem exists_localSection_lift
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : ℂ)
    (hv : v ∈ fixedVectors (characterRepresentation χ)
      (conjOpenSubgroup H K 1).toSubgroup) :
    ∃ φ : SchwartzBruhat G, ∀ g : G,
      characterOrbitIntegral H μH χ φ g =
        eval H (characterRepresentation χ)
          (compactDoubleCosetSection H (characterRepresentation χ) K hK 1 v hv).1 g := by
  classical
  let S : Set H := {h | (h : G) ∈ K}
  have hSo : IsOpen S := K.isOpen.preimage continuous_subtype_val
  have hSc : IsCompact S := by
    simpa only [inv_one, one_mul, mul_one] using
      QuotientIntegration.isCompact_compactOpenOrbitStabilizer H hH K hK (1 : G)
  have hcpos : 0 < μH S := hSo.measure_pos μH ⟨1, K.one_mem⟩
  have hcfin : μH S < ⊤ := hSc.measure_lt_top
  let c : ℂ := ((μH S).toReal : ℂ)
  have hc : c ≠ 0 := by
    change ((μH S).toReal : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (ENNReal.toReal_pos hcpos.ne' hcfin.ne))
  let φ : SchwartzBruhat G := (v / c) • Hecke.TestFunction.subgroupIndicator K hK
  have hi : characterOrbitIntegral H μH χ φ 1 = v := by
    have he : (fun h : H => (((χ h)⁻¹ : ℂˣ) : ℂ) * φ ((h : G) * 1)) =
        S.indicator (fun _ => v / c) := by
      funext h
      by_cases hh : (h : G) ∈ K
      · have hf := hv ⟨h, mem_conjOpenSubgroup.mpr (by simpa using hh)⟩
        change (χ h : ℂ) * v = v at hf
        have hf' : (((χ h)⁻¹ : ℂˣ) : ℂ) * v = v := by
          calc
            _ = (((χ h)⁻¹ : ℂˣ) : ℂ) * ((χ h : ℂ) * v) := by rw [hf]
            _ = v := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        change (((χ h)⁻¹ : ℂˣ) : ℂ) *
          ((v / c) * Hecke.TestFunction.subgroupIndicator K hK ((h : G) * 1)) = _
        rw [mul_one, Hecke.TestFunction.subgroupIndicator_apply, Set.indicator_of_mem hh,
          mul_one, Set.indicator_of_mem (show h ∈ S from hh), ← mul_div_assoc, hf']
      · simp [φ, Hecke.TestFunction.subgroupIndicator_apply, hh, S]
    rw [characterOrbitIntegral, he,
      integral_indicator_const _ hSo.measurableSet]
    change c * (v / c) = v
    exact mul_div_cancel₀ v hc
  have hiK (k : K) : characterOrbitIntegral H μH χ φ (k : G) = v := by
    have he : Hecke.TestFunction.rightTranslate (k : G) φ = φ := by
      apply Hecke.TestFunction.ext
      intro x
      change (v / c) * Hecke.TestFunction.subgroupIndicator K hK (x * (k : G)) =
        (v / c) * Hecke.TestFunction.subgroupIndicator K hK x
      rw [(Hecke.TestFunction.subgroupIndicator_mem K hK).2 k x]
    calc
      _ = characterOrbitIntegral H μH χ φ (1 * (k : G)) := by rw [one_mul]
      _ = characterOrbitIntegral H μH χ
          (Hecke.TestFunction.rightTranslate (k : G) φ) 1 :=
        (characterOrbitIntegral_translate H μH χ φ (k : G) 1).symm
      _ = v := by rw [he, hi]
  refine ⟨φ, fun g => ?_⟩
  by_cases hg : ∃ p : H, ∃ k : K, g = (p : G) * (k : G)
  · obtain ⟨p, k, rfl⟩ := hg
    rw [characterOrbitIntegral_left, hiK]
    have hp := compactDoubleCosetSection_apply H (characterRepresentation χ) K hK 1 v hv p k
    change eval H (characterRepresentation χ)
      (compactDoubleCosetSection H (characterRepresentation χ) K hK 1 v hv).1
        ((p : G) * 1 * (k : G)) = (χ p : ℂ) * v at hp
    simpa only [mul_one] using hp.symm
  · have hφ : ∀ h : H, φ ((h : G) * g) = 0 := by
      intro h
      have hn : (h : G) * g ∉ K := by
        intro hh
        apply hg
        exact ⟨h⁻¹, ⟨(h : G) * g, hh⟩, by simp⟩
      simp [φ, Hecke.TestFunction.subgroupIndicator_apply, hn]
    have hsection : eval H (characterRepresentation χ)
        (compactDoubleCosetSection H (characterRepresentation χ) K hK 1 v hv).1 g = 0 := by
      by_contra hn
      obtain ⟨k, hk, hq⟩ := compactDoubleCosetSection_support_subset H
        (characterRepresentation χ) K hK 1 v hv ⟨g, hn, rfl⟩
      have hp : g * (1 * k)⁻¹ ∈ H :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
      apply hg
      exact ⟨⟨_, hp⟩, ⟨k, hk⟩, by simp [mul_assoc]⟩
    simp [characterOrbitIntegral, hφ, hsection]

include hH hχ in
private def liftableFunctions :
    Submodule ℂ (CompactFunctions H (characterRepresentation χ)) where
  carrier := {f | ∃ φ : SchwartzBruhat G, ∀ g,
    characterOrbitIntegral H μH χ φ g = eval H (characterRepresentation χ) f.1 g}
  zero_mem' := ⟨0, fun g => by simp [characterOrbitIntegral, eval]⟩
  add_mem' := by
    rintro f₁ f₂ ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    refine ⟨φ₁ + φ₂, fun g => ?_⟩
    rw [characterOrbitIntegral_add H hH μH χ hχ, hφ₁, hφ₂]
    rfl
  smul_mem' := by
    rintro c f ⟨φ, hφ⟩
    refine ⟨c • φ, fun g => ?_⟩
    rw [characterOrbitIntegral_smul, hφ]
    rfl

include hH hχ in
/-- Every actual smooth compact-modulo-H character-covariant function is the
character average of a compactly supported locally constant group test. -/
theorem exists_characterOrbitIntegral_eq
    (hbasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (f : CompactFunctions H (characterRepresentation χ)) :
    ∃ φ : SchwartzBruhat G, ∀ g : G,
      characterOrbitIntegral H μH χ φ g = eval H (characterRepresentation χ) f.1 g := by
  have hspan := compactLocalSectionSpanning G hbasis H hH ℂ (characterRepresentation χ)
  have hle : Submodule.span ℂ
      {f : CompactFunctions H (characterRepresentation χ) |
        ∃ (a : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
          (v : ℂ) (hv : v ∈ fixedVectors (characterRepresentation χ)
            (conjOpenSubgroup H K 1).toSubgroup),
          f = compactInduced H (characterRepresentation χ) a
            (compactDoubleCosetSection H (characterRepresentation χ) K hK 1 v hv)}
      ≤ liftableFunctions H hH μH χ hχ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, K, hK, v, hv, rfl⟩
    obtain ⟨φ, hφ⟩ := exists_localSection_lift H hH μH χ K hK v hv
    refine ⟨Hecke.TestFunction.rightTranslate a φ, fun g => ?_⟩
    rw [characterOrbitIntegral_translate, hφ]
    rfl
  rw [hspan] at hle
  exact hle (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ _))

end Langlands.RankinSelberg.CompactWhittakerSynthesis
