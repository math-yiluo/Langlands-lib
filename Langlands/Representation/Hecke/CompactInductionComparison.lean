import Langlands.Representation.Hecke.CompactInductionRightFormula
import Langlands.Representation.Induction.CompactQuotientProof

/-! The subgroup-test construction of the III.2.6 comparison. -/

noncomputable section

open MeasureTheory CategoryTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))

/-- Restriction of a left translate to the closed subgroup, weighted by the
exact relative modular character. -/
def compactSubgroupTest (g : G) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat H where
  toFun T :=
    ⟨fun h => ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) *
        T (g⁻¹ * (h : G)),
      (haarScale_locallyConstant.mul
        (haarScale_locallyConstant.comp_continuous continuous_subtype_val.inv)).mul
        (T.locallyConstant.comp_continuous (continuous_const.mul continuous_subtype_val)),
      ((T.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft g⁻¹)).comp_isClosedEmbedding
        hH.isClosedEmbedding_subtypeVal).mul_left⟩
  map_add' T S := by ext h; simp [mul_add]
  map_smul' c T := by ext h; simp [mul_left_comm]

@[simp] theorem compactSubgroupTest_apply (g : G) (T : SchwartzBruhat G) (h : H) :
    compactSubgroupTest H hH g T h =
      ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) *
        T (g⁻¹ * (h : G)) := rfl

/-- The test functions transform on the left by the relative character. -/
theorem compactSubgroupTest_covariant (h : H) (g : G) (T : SchwartzBruhat G) :
    compactSubgroupTest H hH ((h : G) * g) T =
      ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) •
        TestFunction.leftTranslate h (compactSubgroupTest H hH g T) := by
  ext t
  let χ := (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom
  have hc : (χ h : ℂ) * (χ (h⁻¹ * t) : ℂ) = (χ t : ℂ) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  change (χ t : ℂ) * T (((h : G) * g)⁻¹ * (t : G)) =
    (χ h : ℂ) * ((χ (h⁻¹ * t) : ℂ) * T (g⁻¹ * ((h⁻¹ * t : H) : G)))
  rw [← mul_assoc, hc]
  simp only [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]

variable (μH : Measure H) [μH.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- Elementary comparison value, using the algebraic finite-fiber integral. -/
def compactComparisonValue (T : SchwartzBruhat G) (w : V) (g : G) : V :=
  integratedAction μH ρ hρ (compactSubgroupTest H hH g T) w

/-- Covariance is obtained directly from left translation of the integrated
subgroup action. -/
theorem compactComparisonValue_covariant (T : SchwartzBruhat G) (w : V) (h : H) (g : G) :
    compactComparisonValue H hH μH ρ hρ T w ((h : G) * g) =
      Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ h
          (compactComparisonValue H hH μH ρ hρ T w g) := by
  unfold compactComparisonValue
  rw [compactSubgroupTest_covariant, map_smul, LinearMap.smul_apply,
    integratedAction_leftTranslate]
  rfl

/-- A left stabilizer of T becomes a uniform right stabilizer of the output. -/
theorem compactComparisonValue_mul (T : SchwartzBruhat G) (w : V) (K : OpenSubgroup G)
    (hK : ∀ k : K, ∀ x, T ((k : G) * x) = T x) (k : K) (g : G) :
    compactComparisonValue H hH μH ρ hρ T w (g * (k : G)) =
      compactComparisonValue H hH μH ρ hρ T w g := by
  unfold compactComparisonValue
  congr 2
  ext h
  simp only [compactSubgroupTest_apply, mul_inv_rev, mul_assoc]
  exact congrArg
    (fun z => ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) * z)
    (hK ⟨(k : G)⁻¹, K.inv_mem k.property⟩ (g⁻¹ * (h : G)))

/-- The elementary comparison as a function with a single open stabilizer. -/
def compactComparisonSmooth (T : SchwartzBruhat G) (w : V) :
    Induction.SmoothFunctions H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) := by
  classical
  let hex := TestFunction.commonCompactOpenBiInvariance G {T} ⊤
  let K := hex.choose
  exact Induction.smoothFunctionOf H _ (compactComparisonValue H hH μH ρ hρ T w)
    (compactComparisonValue_covariant H hH μH ρ hρ T w) K
    (compactComparisonValue_mul H hH μH ρ hρ T w K (hex.choose_spec.2.2 T (by simp)).1)

@[simp] theorem compactComparisonSmooth_eval (T : SchwartzBruhat G) (w : V) (g : G) :
    Induction.eval H _ (compactComparisonSmooth H hH μH ρ hρ T w) g =
      compactComparisonValue H hH μH ρ hρ T w g := by
  rfl

/-- Nonzero comparison values lie over the inverse of the support of T. -/
theorem compactComparisonValue_support (T : SchwartzBruhat G) (w : V) :
    Induction.quotientSupport H (compactComparisonValue H hH μH ρ hρ T w) ⊆
      (fun x => Induction.quotientMap H x⁻¹) '' Function.support T := by
  classical
  rintro _ ⟨g, hg, rfl⟩
  have hex : ∃ h : H, T (g⁻¹ * (h : G)) ≠ 0 := by
    by_contra! hn
    have ht : compactSubgroupTest H hH g T = 0 := by
      ext h
      simp only [compactSubgroupTest_apply, hn, mul_zero]
      rfl
    apply hg
    unfold compactComparisonValue
    rw [ht, map_zero]
    rfl
  obtain ⟨h, hh⟩ := hex
  refine ⟨g⁻¹ * (h : G), hh, ?_⟩
  apply Quotient.sound
  change QuotientGroup.rightRel H ((g⁻¹ * (h : G))⁻¹) g
  rw [QuotientGroup.rightRel_apply]
  simpa only [inv_inv, mul_inv_cancel_left] using h.property

/-- The projected support is a closed subset of the compact image of the
inverse support of T. -/
theorem compactComparisonSmooth_compact (T : SchwartzBruhat G) (w : V) :
    IsCompact (Induction.quotientSupport H
      (Induction.eval H _ (compactComparisonSmooth H hH μH ρ hρ T w))) := by
  apply ((TestFunction.isCompact_support T).image
    ((continuous_quot_mk : Continuous (Induction.quotientMap H)).comp continuous_inv)
    ).of_isClosed_subset (Induction.isClosed_quotientSupport H _ _) 
  exact compactComparisonValue_support H hH μH ρ hρ T w

/-- The elementary comparison lands in the original compact function model. -/
def compactComparisonFunction (T : SchwartzBruhat G) (w : V) :
    Induction.CompactFunctions H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) :=
  ⟨compactComparisonSmooth H hH μH ρ hρ T w,
    compactComparisonSmooth_compact H hH μH ρ hρ T w⟩

@[simp] theorem compactComparisonFunction_eval (T : SchwartzBruhat G) (w : V) (g : G) :
    Induction.eval H _ (compactComparisonFunction H hH μH ρ hρ T w).val g =
      compactComparisonValue H hH μH ρ hρ T w g := rfl

/-- The actual elementary map is complex-bilinear. -/
def compactComparisonBilinear :
    SchwartzBruhat G →ₗ[ℂ] V →ₗ[ℂ]
      Induction.CompactFunctions H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) where
  toFun T :=
    { toFun := compactComparisonFunction H hH μH ρ hρ T
      map_add' := by
        intro v w
        ext g
        change compactComparisonValue H hH μH ρ hρ T (v + w) g = _
        exact map_add (integratedAction μH ρ hρ (compactSubgroupTest H hH g T)) v w
      map_smul' := by
        intro c w
        ext g
        change compactComparisonValue H hH μH ρ hρ T (c • w) g = _
        exact map_smul (integratedAction μH ρ hρ (compactSubgroupTest H hH g T)) c w }
  map_add' := by
    intro T S
    ext w g
    change integratedAction μH ρ hρ (compactSubgroupTest H hH g (T + S)) w = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    intro c T
    ext w g
    change integratedAction μH ρ hρ (compactSubgroupTest H hH g (c • T)) w = _
    simp only [map_smul, LinearMap.smul_apply]
    rfl

end Langlands.Hecke.Homomorphism
