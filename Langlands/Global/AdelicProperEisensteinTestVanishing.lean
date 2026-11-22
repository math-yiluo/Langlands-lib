import Langlands.Global.AdelicParabolicPeriodVanishing
import Langlands.Global.EisensteinConstantTerm.Reduction

/-! # A proper parabolic Eisenstein term has zero cuspidal test -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal ComplexConjugate Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P L U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (p : P ⟶ G)

local notation "M" => normOneSubgroup F G
local notation "Γ" => rationalNormOneSubgroup F G
local notation "Λ" => parabolicRationalNormOneSubgroup p
local notation "Cosets" => EisensteinConstantTerm.AmbientCosets Γ Λ

/-- The actual sum over `P(F) \ G(F)`, weighted by a norm-one Levi test. -/
def properEisensteinTestSum
    (f test : AdelicGroupPoints F G → ℂ) (m : M) : ℂ :=
  (∑' c : Cosets, f (((c.out : Γ).val * m) : M).val) * conj (test m.val)

/-- The nonnegative sum that controls the absolute integral after unfolding. -/
def properEisensteinTestAbsoluteSum
    (f test : AdelicGroupPoints F G → ℂ) (m : M) : ℝ≥0∞ :=
  ∑' c : Cosets, ‖f (((c.out : Γ).val * m) : M).val * conj (test m.val)‖ₑ

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem parabolicRationalNormOneSubgroup_le :
    (parabolicRationalNormOneSubgroup p : Subgroup M) ≤ Γ := by
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact ⟨P.affinePointsTarget p _ z, (mapNormOne_rationalNormOne F P G p z).symm⟩

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem properEisensteinTestProduct_invariant (f test : AdelicGroupPoints F G → ℂ)
    (hf : IsLeftInvariantUnder F G (rationalImage F p) f)
    (htest : IsLeftInvariantUnder F G (rationalSubgroup F G) test) :
    ∀ x ∈ Λ, ∀ m : M, f (x * m).val * conj (test (x * m).val) =
      f m.val * conj (test m.val) := by
  intro x hx m
  obtain ⟨z, hz⟩ := parabolicRationalNormOneSubgroup_le p hx
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hx
  change f (x.val * m.val) * conj (test (x.val * m.val)) = _
  rw [hf _ ⟨y, congrArg Subtype.val hy⟩, htest _ ⟨z, congrArg Subtype.val hz⟩]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The absolute tested coset sum is independent of the rational representative. -/
theorem properEisensteinTestAbsoluteSum_mul (f test : AdelicGroupPoints F G → ℂ)
    (hf : IsLeftInvariantUnder F G (rationalImage F p) f)
    (htest : IsLeftInvariantUnder F G (rationalSubgroup F G) test)
    (x : Γ) (m : M) :
    properEisensteinTestAbsoluteSum p f test (x.val * m) =
      properEisensteinTestAbsoluteSum p f test m := by
  let H : M → ℝ≥0∞ := fun y => ‖f y.val * conj (test y.val)‖ₑ
  have hH : ∀ z ∈ Λ, ∀ y, H (z * y) = H y := fun z hz y =>
    congrArg (fun b : ℂ => ‖b‖ₑ) (properEisensteinTestProduct_invariant p f test hf htest z hz y)
  have ht (c : Cosets) (y : M) :
      H ((c.out : Γ).val * y) = ‖f ((c.out : Γ).val * y).val * conj (test y.val)‖ₑ := by
    obtain ⟨t, ht⟩ := c.out.property
    change ‖f ((c.out : Γ).val * y).val *
      conj (test ((c.out : Γ).val.val * y.val))‖ₑ = _
    rw [htest _ ⟨t, congrArg Subtype.val ht⟩]
  unfold properEisensteinTestAbsoluteSum
  simp_rw [← ht]
  exact EisensteinConstantTerm.tsum_out_mul_left hH x.property m

variable [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom] [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
  (l : L ⟶ P) (iU : U ⟶ P)
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion (iU ≫ p).hom.hom.left]

/-- After unfolding an absolutely integrable proper parabolic coset sum
against a test with zero radical constant term, its norm-one quotient
integral vanishes. A uniform bound at one representative of each ambient
rational coset suffices for absolute integrability. -/
def ProperEisensteinTestVanishingStatement : Prop :=
  LeviSubgroup.IsGeometricUnipotentRadical iU →
  IsIso (subgroupMultiplication l iU) →
  IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) →
  IsFiniteMeasure (normOneRationalQuotientHaarMeasure F P) →
  IsFiniteMeasure (normOneRationalQuotientHaarMeasure F L) →
  ∀ f test : AdelicGroupPoints F G → ℂ, Continuous f → Continuous test →
    IsLeftInvariantUnder F G (rationalImage F p) f →
    IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) f →
    IsLeftInvariantUnder F G (rationalSubgroup F G) test →
    subgroupConstantTerm F (iU ≫ p) test = 0 →
    (∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ q : NormOneRationalQuotient F G,
      ∃ m : M, LeftCosetSpace.mk Γ m = q ∧ properEisensteinTestAbsoluteSum p f test m ≤ B) →
    let pair := fun q : NormOneRationalQuotient F G => properEisensteinTestSum p f test q.out
    Integrable pair (normOneRationalQuotientHaarMeasure F G) ∧
      ∫ q, pair q ∂normOneRationalQuotientHaarMeasure F G = 0

set_option maxHeartbeats 1100000 in
theorem properEisensteinTestVanishing : ProperEisensteinTestVanishingStatement p l iU := by
  intro hU hsplit hG hP hL f test hf ht hfP hfU htG ht0 hbound pair
  let hΓ := isDiscrete_rationalNormOneSubgroup F G
  let hΛ := isDiscrete_parabolicRationalNormOneSubgroup p
  let mH : Measure M := Measure.haar
  let T := LeftCosetSpace.fundamentalDomain Γ hΓ
  let funG : AdelicGroupPoints F G → ℂ := fun x => f x * conj (test x)
  let funM : M → ℂ := fun x => funG x.val
  have hfG : Continuous funG := hf.mul (Complex.continuous_conj.comp ht)
  have hfM : Measurable funM := (hfG.comp continuous_subtype_val).measurable
  have hInv (a : Λ) (m : M) : funM (a.val * m) = funM m :=
    properEisensteinTestProduct_invariant p f test hfP htG a.val a.property m
  let ρ : Cosets → M := fun c => (c.out : Γ).val
  have hρ : ∀ x ∈ Γ, ∃! c, x * (ρ c)⁻¹ ∈ Λ :=
    RankinSelbergGlobal.Unfolding.existsUnique_cosetRep Λ Γ
  let : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  let : Countable Cosets := inferInstance
  have htTrans (c : Cosets) (m : M) : test (ρ c * m).val = test m.val := by
    obtain ⟨z, hz⟩ := (c.out : Γ).property
    exact htG _ ⟨z, congrArg Subtype.val hz⟩ m.val
  have hterm (m : M) :
      properEisensteinTestSum p f test m = ∑' c, funM (ρ c * m) := by
    unfold properEisensteinTestSum
    rw [← tsum_mul_right]
    apply tsum_congr
    intro c
    change f (ρ c * m).val * conj (test m.val) = f (ρ c * m).val * conj (test (ρ c * m).val)
    rw [htTrans]
  have hAbs (m : M) : (∑' c, ‖funM (ρ c * m)‖ₑ) = properEisensteinTestAbsoluteSum p f test m := by
    unfold properEisensteinTestAbsoluteSum
    apply tsum_congr
    intro c
    change ‖f (ρ c * m).val * conj (test (ρ c * m).val)‖ₑ =
      ‖f (ρ c * m).val * conj (test m.val)‖ₑ
    rw [htTrans]
  obtain ⟨B, hB, hrep⟩ := hbound
  have hBound (m : M) : (∑' c, ‖funM (ρ c * m)‖ₑ) ≤ B := by
    rw [hAbs]
    obtain ⟨x, hx, hBx⟩ := hrep (LeftCosetSpace.mk Γ m)
    have hδ : m * x⁻¹ ∈ Γ := (LeftCosetSpace.mk_eq_mk_iff Γ x m).mp hx
    have hE : (⟨m * x⁻¹, hδ⟩ : Γ).val * x = m := inv_mul_cancel_right m x
    rw [← hE, properEisensteinTestAbsoluteSum_mul p f test hfP htG]
    exact hBx
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure Γ hΓ) := hG
  have hfin : ∫⁻ m in T, ∑' c, ‖funM (ρ c * m)‖ₑ ∂mH ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hB (LeftCosetSpace.haar_fundamentalDomain_ne_top Γ hΓ))
    exact (lintegral_mono hBound).trans_eq (setLIntegral_const T B)
  obtain ⟨hIntOut, hInt, hEq⟩ := EisensteinConstantTerm.integral_unfold mH
    (LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ)
    (LeftCosetSpace.fundamentalDomain_unique Γ hΓ) ρ (fun c => c.out.property) hρ hfM hInv hfin
  let A := ⋃ c, ρ c • T
  have hA := EisensteinConstantTerm.isFundamentalDomain_iUnion_smul
    (parabolicRationalNormOneSubgroup_le p) (LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ)
    (LeftCosetSpace.fundamentalDomain_unique Γ hΓ) ρ (fun c => c.out.property) hρ mH
  have hIntA : IntegrableOn funM A mH :=
    (RankinSelbergGlobal.Unfolding.integrable_out_iff Λ hfM hInv mH A).mp hIntOut
  let : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  have hΛdom := LeftCosetSpace.isFundamentalDomain Λ hΛ mH
  have hIntΛ := (hΛdom.integrableOn_iff hA hInv).2 hIntA
  have hCT : subgroupConstantTerm F (iU ≫ p) funG = 0 := by
    funext x
    let conjTest : AdelicGroupPoints F G → ℂ := fun z => conj (test z)
    have hCTconj : subgroupConstantTerm F (iU ≫ p) conjTest x = 0 := by
      unfold subgroupConstantTerm conjTest
      rw [integral_conj]
      change conj (subgroupConstantTerm F (iU ≫ p) test x) = 0
      simp only [congrFun ht0 x, Pi.zero_apply, map_zero]
    have hU' : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)),
        ∀ y, f (u * y) = f y := by
      intro u hu y
      exact hfU u hu y
    change subgroupConstantTerm F (iU ≫ p) (fun z => f z * conjTest z) x = 0
    simp_rw [mul_comm (f _)]
    rw [EisensteinConstantTerm.subgroupConstantTerm_mul_invariant (iU ≫ p) conjTest f hU',
      hCTconj, zero_mul]
  have hZero := adelicParabolicPeriodVanishing p l iU hU hsplit hG hP hL
    funG hfG (fun z hz x => by
      have hz' := rationalImage_le_rationalSubgroup p hz
      change f (z * x) * conj (test (z * x)) = _
      rw [hfP z hz x, htG z hz' x]) hIntΛ hCT
  rw [RankinSelbergGlobal.Unfolding.integral_out_eq Λ hfM hInv mH A,
    hA.setIntegral_eq hΛdom hInv, hZero] at hEq
  have hSInv (a : Γ) (m : M) : properEisensteinTestSum p f test (a.val * m) =
      properEisensteinTestSum p f test m := by
    rw [hterm, hterm]
    exact EisensteinConstantTerm.tsum_out_mul_left (fun x hx y => hInv ⟨x, hx⟩ y) a.property m
  have hSm : Measurable (properEisensteinTestSum p f test) := by
    rw [funext hterm]
    exact Measurable.tsum fun _ => hfM.comp (measurable_const_mul _)
  have hPair : pair = LeftCosetSpace.lift Γ (properEisensteinTestSum p f test) hSInv :=
    RankinSelbergGlobal.Unfolding.out_eq_lift Γ _ _
  have hpairM : Measurable pair := hPair ▸ measurable_from_quotient.mpr hSm
  have hRep (m : M) : pair (LeftCosetSpace.mk Γ m) = ∑' c, funM (ρ c * m) := by
    rw [hPair]
    exact hterm m
  constructor
  · apply (LeftCosetSpace.integrable_quotientMeasure_iff Γ mH T pair hpairM.aestronglyMeasurable).2
    simpa only [hRep] using hInt
  · change (∫ q, pair q ∂LeftCosetSpace.quotientMeasure Γ mH T) = 0
    rw [LeftCosetSpace.integral_quotientMeasure Γ mH T pair hpairM.aestronglyMeasurable]
    simpa only [hRep] using hEq.symm

end Langlands.Global
