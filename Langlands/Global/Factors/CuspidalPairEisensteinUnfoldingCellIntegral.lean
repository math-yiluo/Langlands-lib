import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingSeries
import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingVanishing

/-! # Unfolding the generic coefficient cell by cell

On `N₀(𝔸)`, the sum over `Λ_J(F) \ N₀(F)` of the terms of the Eisenstein sum in the cell `J`,
integrated against the conjugate generic character over a fundamental domain of `N₀(F)`, unfolds
to the integral of `φ_s(γ_J n) conj(ψ_N(n))` over a fundamental domain of `Λ_J(F)`. For `J`
different from the open cell this integral vanishes. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped ENNReal Pointwise

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon PrimitiveAdelicHeight

local instance cellIntegralSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance cellIntegralSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section Abstract

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H] (μ : Measure H)
  [μ.IsMulLeftInvariant]

/-- Integrability on the union of translates of a fundamental domain of finite measure, from a
uniform bound on the orbit sums of the norms. -/
theorem integrableOn_iUnion_of_tsum_le {Λ Γ : Subgroup H} {s : Set H} (hsm : MeasurableSet s)
    (hs : ∀ x, ∃! c : Γ, (c : H) * x ∈ s) (hμs : μ s ≠ ∞)
    {ι : Type*} [Countable ι] (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ c ∈ Γ, ∃! i, c * (ρ i)⁻¹ ∈ Λ) {f : H → ℂ} (hfm : Measurable f) (B : ℝ)
    (hsum : ∀ x, Summable fun i => ‖f (ρ i * x)‖) (hB : ∀ x, ∑' i, ‖f (ρ i * x)‖ ≤ B) :
    IntegrableOn f (⋃ i, ρ i • s) μ := by
  have hdisj := RankinSelbergGlobal.Unfolding.pairwise_disjoint_smul (Λ := Λ) hs ρ hρΓ hρ
  have hmeas : ∀ i, MeasurableSet (ρ i • s) := fun i => hsm.const_smul (ρ i)
  have hmp : ∀ i, MeasurePreserving (fun x => ρ i * x) μ μ := fun i =>
    measurePreserving_mul_left μ (ρ i)
  have hemb : ∀ i, MeasurableEmbedding (fun x : H => ρ i * x) := fun i =>
    measurableEmbedding_mulLeft (ρ i)
  have hpre : ∀ i, (fun x : H => ρ i * x) ⁻¹' (ρ i • s) = s := fun i => by
    ext x
    simp [mem_smul_set_iff_inv_smul_mem]
  have hlint : ∀ i, ∫⁻ x in ρ i • s, ‖f x‖ₑ ∂μ = ∫⁻ x in s, ‖f (ρ i * x)‖ₑ ∂μ := fun i => by
    conv_rhs => rw [← hpre i]
    exact ((hmp i).setLIntegral_comp_preimage_emb (hemb i) (fun x => ‖f x‖ₑ) (ρ i • s)).symm
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  change ∫⁻ x in ⋃ i, ρ i • s, ‖f x‖ₑ ∂μ < ∞
  rw [lintegral_iUnion hmeas hdisj]
  simp_rw [hlint]
  rw [← lintegral_tsum (f := fun i x => ‖f (ρ i * x)‖ₑ)
    fun i => ((hfm.comp (measurable_const_mul (ρ i))).enorm).aemeasurable]
  have hle : ∀ x, ∑' i, ‖f (ρ i * x)‖ₑ ≤ ENNReal.ofReal B := by
    intro x
    have h1 : ∑' i, ‖f (ρ i * x)‖ₑ = ENNReal.ofReal (∑' i, ‖f (ρ i * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum x)]
      simp
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hB x)
  calc ∫⁻ x in s, ∑' i, ‖f (ρ i * x)‖ₑ ∂μ ≤ ∫⁻ _x in s, ENNReal.ofReal B ∂μ := lintegral_mono hle
    _ = ENNReal.ofReal B * μ s := by rw [setLIntegral_const]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμs.lt_top

end Abstract

section GenericCharacter

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

/-- The generic character `ψ_N(n) = ψ(n_(0,1) + ⋯ + n_(N-2,N-1))` on `N₀(𝔸)`. -/
def genericChar (ψ : AddChar (Adeles F) ℂ) (x : unipotentAdelic F (r + t + 2)) : ℂ :=
  ψ (∑ i : Fin (r + t + 1), (toMat F (r + t + 2) x :
    Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) i.castSucc i.succ)

theorem genericChar_mul (ψ : AddChar (Adeles F) ℂ) (x y : unipotentAdelic F (r + t + 2)) :
    genericChar ψ (x * y) = genericChar ψ x * genericChar ψ y := by
  simp only [genericChar]
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Units.val_mul]
  exact RankinSelbergGlobal.Unfolding.superdiag_mul_of_isUnitriangular (isUnitriangular_toMat F _ x)
    (isUnitriangular_toMat F _ y) i

theorem genericChar_ratHom (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (δ : GeneralLinear.upperUnipotent (r + t + 2) F) : genericChar ψ (ratHom F _ δ) = 1 := by
  simp only [genericChar, toMat_ratHom, AdelicGL.rational_apply]
  rw [← map_sum]
  exact hψ _

theorem genericChar_of_mem_Γ₀ (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) {x : unipotentAdelic F (r + t + 2)}
    (hx : x ∈ Γ₀ F (r + t + 2)) : genericChar ψ x = 1 := by
  obtain ⟨δ, rfl⟩ := (mem_Γ₀_iff F _ x).mp hx
  exact genericChar_ratHom ψ hψ δ

theorem continuous_genericChar (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ) :
    Continuous (genericChar (r := r) (t := t) ψ) := by
  have h1 : Continuous fun x : unipotentAdelic F (r + t + 2) => (toMat F (r + t + 2) x :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) :=
    Units.continuous_val.comp (continuous_toMat F _)
  exact hψ.comp (continuous_finsetSum _ fun i _ => h1.matrix_elem _ _)

theorem norm_genericChar (ψ : AddChar (Adeles F) ℂ) (hψ : ∀ a : Adeles F, ‖ψ a‖ = 1)
    (x : unipotentAdelic F (r + t + 2)) : ‖genericChar ψ x‖ = 1 :=
  hψ _

end GenericCharacter

section Cells

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}

/-- The representatives `δ_q` of `Λ_J(F) \ N₀(F)` in `N₀(𝔸)`. -/
def cosetRep (J : PivotIndex (r + t + 2) (r + 1)) (q : StabilizerCosets (K := F) J.1) :
    unipotentAdelic F (r + t + 2) :=
  ratHom F _ (Quotient.out q)

omit [CompactSpace (AdeleQuotient F)] in
theorem existsUnique_cosetRep (J : PivotIndex (r + t + 2) (r + 1))
    (c : unipotentAdelic F (r + t + 2)) (hc : c ∈ Γ₀ F (r + t + 2)) :
    ∃! q : StabilizerCosets (K := F) J.1, c * (cosetRep J q)⁻¹ ∈ patternRational F _ J.1 := by
  obtain ⟨δ, rfl⟩ := (mem_Γ₀_iff F _ c).mp hc
  have key : ∀ q : StabilizerCosets (K := F) J.1,
      ratHom F _ δ * (cosetRep J q)⁻¹ ∈ patternRational F _ J.1 ↔
        q = Quotient.mk _ δ := by
    intro q
    rw [cosetRep, ← map_inv, ← map_mul]
    constructor
    · rintro ⟨-, h2⟩
      have h3 := (ratHom_mem_pattern_iff F _ J.1 _).mp h2
      rw [← Quotient.out_eq q]
      apply Quotient.sound
      change QuotientGroup.rightRel _ _ _
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
      exact h3
    · rintro rfl
      refine ⟨ratHom_mem_Γ₀ F _ _, (ratHom_mem_pattern_iff F _ J.1 _).mpr ?_⟩
      have h := Quotient.mk_out (s := QuotientGroup.rightRel
        ((stabilizer (R := F) J.1).subgroupOf (GeneralLinear.upperUnipotent (r + t + 2) F))) δ
      change QuotientGroup.rightRel _ _ _ at h
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h
      exact h
  exact ⟨Quotient.mk _ δ, (key _).mpr rfl, fun q hq => (key q).mp hq⟩

/-- The unfolded integrand `φ_s(γ_J n) conj(ψ_N(n))` of the cell `J`. -/
def cellIntegrand (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) (ψ : AddChar (Adeles F) ℂ)
    (J : PivotIndex (r + t + 2) (r + 1)) (x : unipotentAdelic F (r + t + 2)) : ℂ :=
  twisted φ s (AdelicGL.rational F _ (cellRep r t F J.1) * toMat F _ x) *
    starRingEnd ℂ (genericChar ψ x)

omit [CompactSpace (AdeleQuotient F)] in
theorem cellTerm_mul_conj (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (s : ℂ)
    (J : PivotIndex (r + t + 2) (r + 1)) (q : StabilizerCosets (K := F) J.1)
    (x : unipotentAdelic F (r + t + 2)) :
    cellTerm φ s J q (toMat F _ x) * starRingEnd ℂ (genericChar ψ x) =
      cellIntegrand φ s ψ J (cosetRep J q * x) := by
  rw [cellIntegrand, genericChar_mul, cosetRep, genericChar_ratHom ψ hψ, one_mul, map_mul,
    toMat_ratHom, ← mul_assoc, ← map_mul]
  rfl

theorem continuous_cellIntegrand (hφ : IsSection T T' φ) (s : ℂ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : Continuous ψ) (J : PivotIndex (r + t + 2) (r + 1)) :
    Continuous (cellIntegrand φ s ψ J) :=
  ((continuous_twisted hφ s).comp (continuous_const.mul (continuous_toMat F _))).mul
    (Complex.continuous_conj.comp (continuous_genericChar ψ hψ))

omit [CompactSpace (AdeleQuotient F)] in
theorem countable_stabilizerCosets (J : PivotIndex (r + t + 2) (r + 1)) :
    Countable (StabilizerCosets (K := F) J.1) := by
  have := LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_Γ₀ F (r + t + 2))
  exact Function.Injective.countable (f := fun q => (⟨cosetRep J q, ratHom_mem_Γ₀ F _ _⟩ :
      Γ₀ F (r + t + 2))) (fun q q' h => by
        have h' := congrArg Subtype.val h
        have := ratHom_injective F _ h'
        rw [← Quotient.out_eq q, ← Quotient.out_eq q', this])

/-- The chosen fundamental domain of `N₀(F)` in `N₀(𝔸)`. -/
abbrev fd₀ (F : Type u) [Field F] [NumberField F] (n : ℕ) : Set (unipotentAdelic F n) :=
  LeftCosetSpace.fundamentalDomain (Γ₀ F n) (isDiscrete_Γ₀ F n)

/-- The unfolded domain: a fundamental domain of `Λ_J(F)` in `N₀(𝔸)`. -/
def cellDomain (J : PivotIndex (r + t + 2) (r + 1)) : Set (unipotentAdelic F (r + t + 2)) :=
  ⋃ q : StabilizerCosets (K := F) J.1, cosetRep J q • fd₀ F (r + t + 2)

omit [CompactSpace (AdeleQuotient F)] in
theorem measurableSet_cellDomain (J : PivotIndex (r + t + 2) (r + 1)) :
    MeasurableSet (cellDomain (F := F) J) := by
  have := countable_stabilizerCosets (F := F) J
  exact MeasurableSet.iUnion fun q =>
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _).const_smul _

omit [CompactSpace (AdeleQuotient F)] in
theorem existsUnique_mem_cellDomain (J : PivotIndex (r + t + 2) (r + 1))
    (x : unipotentAdelic F (r + t + 2)) :
    ∃! l : patternRational F _ J.1, (l : unipotentAdelic F (r + t + 2)) * x ∈ cellDomain J :=
  RankinSelbergGlobal.Unfolding.existsUnique_mem_iUnion_smul inf_le_left
    (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_Γ₀ F _)) (cosetRep J)
    (fun _ => ratHom_mem_Γ₀ F _ _) (existsUnique_cosetRep J) x

omit [CompactSpace (AdeleQuotient F)] in
theorem haar_fd₀_ne_top (n : ℕ) :
    (Measure.haar : Measure (unipotentAdelic F n)) (fd₀ F n) ≠ ∞ := by
  have := RankinSelbergGlobal.Unfolding.compactSpace_unipotentRationalQuotient F n
  have h := RankinSelbergGlobal.Unfolding.haar_unipotentFundamentalDomain F n
  change (Measure.haar : Measure (unipotentAdelic F n))
    (RankinSelbergGlobal.Unfolding.unipotentFundamentalDomain F n) ≠ ∞
  rw [h]
  exact ENNReal.inv_ne_top.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero _ _ _)

variable {σ : ℝ}

/-- **Unfolding one cell.** -/
theorem unfold_cell (hφ : IsSection T T' φ) (hσ : NormalBound φ σ) {s : ℂ} (hs : σ < s.re)
    (ψ : AddChar (Adeles F) ℂ) (hψ : RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ)
    (J : PivotIndex (r + t + 2) (r + 1)) :
    IntegrableOn (cellIntegrand φ s ψ J) (cellDomain J) Measure.haar ∧
    IntegrableOn (fun x => (∑' q, cellTerm φ s J q (toMat F _ x)) *
      starRingEnd ℂ (genericChar ψ x)) (fd₀ F (r + t + 2)) Measure.haar ∧
    ∫ x in fd₀ F (r + t + 2), (∑' q, cellTerm φ s J q (toMat F _ x)) *
      starRingEnd ℂ (genericChar ψ x) ∂Measure.haar =
      ∫ x in cellDomain J, cellIntegrand φ s ψ J x ∂Measure.haar := by
  obtain ⟨B, hB⟩ := exists_bound_unipotent hφ hσ hs
  have := countable_stabilizerCosets (F := F) J
  have hnorm : ∀ q x, ‖cellIntegrand φ s ψ J (cosetRep J q * x)‖ =
      ‖cellTerm φ s J q (toMat F _ x)‖ := by
    intro q x
    rw [← cellTerm_mul_conj ψ hψ.2.2.1 s J q x, norm_mul, Complex.norm_conj,
      norm_genericChar ψ hψ.2.2.2, mul_one]
  have hint : IntegrableOn (cellIntegrand φ s ψ J) (cellDomain J) Measure.haar := by
    refine integrableOn_iUnion_of_tsum_le Measure.haar (Λ := patternRational F _ J.1)
      (Γ := Γ₀ F _) (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
      (LeftCosetSpace.fundamentalDomain_unique _ _) (haar_fd₀_ne_top _) (cosetRep J)
      (fun _ => ratHom_mem_Γ₀ F _ _) (existsUnique_cosetRep J)
      (continuous_cellIntegrand hφ s ψ hψ.1 J).measurable B (fun x => ?_) (fun x => ?_)
    · simp_rw [hnorm]
      exact (cellTerm_fiber_le hφ hσ hs J (toMat F _ x)).1
    · simp_rw [hnorm]
      exact (cellTerm_fiber_le hφ hσ hs J _).2.trans (hB x)
  obtain ⟨h1, h2⟩ := RankinSelbergGlobal.Unfolding.integrableOn_tsum_and_setIntegral_eq
    Measure.haar (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
    (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_Γ₀ F _)) (cosetRep J)
    (fun _ => ratHom_mem_Γ₀ F _ _) (existsUnique_cosetRep J) hint
  have hfun : (fun x => ∑' q, cellIntegrand φ s ψ J (cosetRep J q * x)) = fun x =>
      (∑' q, cellTerm φ s J q (toMat F _ x)) * starRingEnd ℂ (genericChar ψ x) := by
    funext x
    rw [← tsum_mul_right]
    simp_rw [cellTerm_mul_conj ψ hψ.2.2.1 s J]
  rw [hfun] at h1 h2
  exact ⟨hint, h1, h2⟩

/-- The unfolded integrand is left invariant under `Λ_J(F)`. -/
theorem cellIntegrand_patternRational_mul (hφ : IsSection T T' φ) (s : ℂ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (J : PivotIndex (r + t + 2) (r + 1)) {l : unipotentAdelic F (r + t + 2)}
    (hl : l ∈ patternRational F _ J.1) (x : unipotentAdelic F (r + t + 2)) :
    cellIntegrand φ s ψ J (l * x) = cellIntegrand φ s ψ J x := by
  obtain ⟨δ, hδ⟩ := (mem_Γ₀_iff F _ _).mp hl.1
  have hδJ : (δ : RationalGL F (r + t + 2)) ∈ stabilizer J.1 :=
    (ratHom_mem_pattern_iff F _ J.1 δ).mp (by rw [hδ]; exact hl.2)
  rw [cellIntegrand, cellIntegrand, ← hδ, genericChar_mul, genericChar_ratHom ψ hψ,
    one_mul, map_mul, toMat_ratHom, ← mul_assoc, ← map_mul]
  have hp := permutation_conj_mem_parabolic (cellPermutation r t J.1) J.1
    (mem_iff_cellPermutation r t J.1 J.2) hδJ
  have : cellRep r t F J.1 * (δ : RationalGL F (r + t + 2)) =
      (GeneralLinear.permutation (r + t + 2) F (cellPermutation r t J.1) *
        (δ : RationalGL F (r + t + 2)) *
        (GeneralLinear.permutation (r + t + 2) F (cellPermutation r t J.1))⁻¹) *
        cellRep r t F J.1 := by
    rw [cellRep]
    group
  rw [this, map_mul, mul_assoc, twisted_rational_mul hφ s _ hp]

/-- **The non-open cells contribute zero.** -/
theorem setIntegral_cellIntegrand_eq_zero (hφ : IsSection T T' φ) (s : ℂ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ)
    (J : PivotIndex (r + t + 2) (r + 1)) (hJ : J.1 ≠ openPivots r t)
    (hint : IntegrableOn (cellIntegrand φ s ψ J) (cellDomain J) Measure.haar) :
    ∫ x in cellDomain J, cellIntegrand φ s ψ J x ∂Measure.haar = 0 := by
  obtain ⟨k, k', hkk', hkJ, hk'J⟩ := exists_simpleRoot_of_ne_openPivots J.1 J.2 hJ
  have hlt : k < k' := by rw [Fin.lt_def]; omega
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, ψ y₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ.2.1 (DFunLike.ext ψ 1 fun y => (h y).trans (AddChar.one_apply y).symm)
  have := countable_patternLattice F _ J.1
  have := haar_pattern_isMulRightInvariant F _ J.1
  have := haar_pattern_isInvInvariant F _ J.1
  have := isFiniteMeasure_patternQuotient F _ J.1
  have hσJ := mem_iff_cellPermutation r t J.1 J.2
  let g₀ : AdelicGL F (r + t + 2) := rootElement k k' hlt.ne y₀
  have hg₀ : g₀ ∈ stabilizer (R := Adeles F) J.1 := rootElement_mem_stabilizer hlt hkJ y₀
  let v₀ : pattern F _ J.1 := ⟨ofMat F _ g₀ hg₀.1, by
    change toMat F _ (ofMat F _ g₀ hg₀.1) ∈ stabilizer J.1
    rw [toMat_ofMat]
    exact hg₀⟩
  have hgc₀ : genericChar ψ (v₀ : unipotentAdelic F (r + t + 2)) = ψ y₀ := by
    simp only [genericChar, v₀, toMat_ofMat]
    rw [sum_superdiag_rootElement (m := r + t + 1) hkk' y₀]
  refine setIntegral_eq_zero_of_mul_right (patternLattice F _ J.1) Measure.haar Measure.haar
    (measurableSet_cellDomain J)
    (RankinSelbergGlobal.Unfolding.existsUnique_of_image _ _
      (mem_patternRational_iff_image F _ J.1) (existsUnique_mem_cellDomain J))
    (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_patternLattice F _ J.1))
    (LeftCosetSpace.fundamentalDomain_unique _ _)
    (LeftCosetSpace.haar_fundamentalDomain_ne_zero _ _)
    (LeftCosetSpace.haar_fundamentalDomain_ne_top _ _)
    (continuous_cellIntegrand hφ s ψ hψ.1 J).measurable ?_ hint v₀ (starRingEnd ℂ (ψ y₀)) ?_ ?_
  · intro l x
    obtain ⟨δ, hδ⟩ := (mem_Γ₀_iff F _ _).mp l.2
    have hδJ : (δ : RationalGL F (r + t + 2)) ∈ stabilizer J.1 :=
      (ratHom_mem_pattern_iff F _ J.1 δ).mp (by rw [hδ]; exact (l : pattern F _ J.1).2)
    have hδ' : ((l : pattern F _ J.1) : unipotentAdelic F (r + t + 2)) = ratHom F _ δ := hδ.symm
    rw [cellIntegrand, cellIntegrand, hδ', genericChar_mul, genericChar_ratHom ψ hψ.2.2.1,
      one_mul, map_mul, toMat_ratHom, ← mul_assoc, ← map_mul]
    have hp := permutation_conj_mem_parabolic (cellPermutation r t J.1) J.1 hσJ hδJ
    have : cellRep r t F J.1 * (δ : RationalGL F (r + t + 2)) =
        (GeneralLinear.permutation (r + t + 2) F (cellPermutation r t J.1) *
          (δ : RationalGL F (r + t + 2)) *
          (GeneralLinear.permutation (r + t + 2) F (cellPermutation r t J.1))⁻¹) *
          cellRep r t F J.1 := by
      rw [cellRep]
      group
    rw [this, map_mul, mul_assoc, twisted_rational_mul hφ s _ hp]
  · intro h
    apply hy₀
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · intro n x
    have hn : toMat F _ (n : unipotentAdelic F (r + t + 2)) ∈ stabilizer (R := Adeles F) J.1 :=
      n.2
    rw [cellIntegrand, cellIntegrand, genericChar_mul, genericChar_mul, genericChar_mul, hgc₀,
      map_mul, map_mul, map_mul, map_mul]
    have hv : toMat F _ (v₀ : unipotentAdelic F (r + t + 2)) = g₀ := toMat_ofMat F _ _ hg₀.1
    rw [hv, rational_cellRep_eq_permutation]
    have hu := permutation_conj_rootElement_mem (cellPermutation r t J.1) J.1 hσJ hn hlt.ne hkJ
      hk'J y₀
    have heq : GeneralLinear.permutation (r + t + 2) (Adeles F) (cellPermutation r t J.1) *
        (toMat F _ (n : unipotentAdelic F (r + t + 2)) * g₀ * toMat F _ x) =
        (GeneralLinear.permutation (r + t + 2) (Adeles F) (cellPermutation r t J.1) *
          (toMat F _ (n : unipotentAdelic F (r + t + 2)) * rootElement k k' hlt.ne y₀ *
            (toMat F _ (n : unipotentAdelic F (r + t + 2)))⁻¹) *
          (GeneralLinear.permutation (r + t + 2) (Adeles F) (cellPermutation r t J.1))⁻¹) *
        (GeneralLinear.permutation (r + t + 2) (Adeles F) (cellPermutation r t J.1) *
          (toMat F _ (n : unipotentAdelic F (r + t + 2)) * toMat F _ x)) := by
      simp only [g₀]
      group
    rw [heq, twisted_unipotent_mul hφ s hu]
    simp only [map_mul]
    ring

end Cells

end Langlands.Global.CuspidalPairEisenstein.Unfolding
