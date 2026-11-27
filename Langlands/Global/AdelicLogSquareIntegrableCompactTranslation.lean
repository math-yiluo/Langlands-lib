import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.RightTranslationTestFunctionSeparationProof

/-! # Infinite compact conjugation of logarithmically square-integrable automorphic forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions RepresentationGrowth

section Height

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "Γ" => rationalSubgroup F G
local notation "σ" => rationalLogHeight F G rho

private theorem rationalLogHeight_mk_eq (g : AdelicGroupPoints F G) :
    σ (LeftCosetSpace.mk Γ g) =
      1 + Real.log (max 1 (⨅ r : Γ, adelicSourceNorm F G rho (r.val * g))) := by
  obtain ⟨q, hq, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) g
  have hinf : (⨅ r : Γ, adelicSourceNorm F G rho (r.val * (q * g))) =
      ⨅ r : Γ, adelicSourceNorm F G rho (r.val * g) := by
    refine (Equiv.mulRight (⟨q, hq⟩ : Γ)).iInf_congr fun r => ?_
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]
  unfold rationalLogHeight
  rw [hout, hinf]

/-- Right translation on the rational quotient increases the logarithmic height by at most
an additive constant. The displayed multiplicative bound follows from `1 ≤ σ`. -/
theorem exists_rationalLogHeight_rightTranslate_le (t : AdelicGroupPoints F G) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : RationalQuotient F G,
      σ (LeftCosetSpace.rightTranslate Γ t y) ≤ C * σ y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hconst (a b : AdelicGroupPoints F G) :
        adelicSourceNorm F G rho a = adelicSourceNorm F G rho b := by
      unfold adelicSourceNorm
      congr 1
      exact Subsingleton.elim _ _
    refine ⟨1, le_rfl, fun y => ?_⟩
    simp only [rationalLogHeight, hconst _ (1 : AdelicGroupPoints F G), one_mul, le_refl]
  · let B := adelicHeight F G rho t
    have hB : 1 ≤ B := one_le_adelicHeight F G rho hN t
    have hBpos : 0 < B := zero_lt_one.trans_le hB
    let s := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hs : 0 < s := pow_pos (Nat.cast_pos.mpr hN) _
    have hmul (g : AdelicGroupPoints F G) :
        adelicSourceNorm F G rho (g * t) ≤ B * adelicSourceNorm F G rho g := by
      have h := adelicHeight_mul_le F G rho hN g t
      change adelicHeight F G rho (g * t) ≤ adelicHeight F G rho g * B at h
      rw [adelicHeight_eq_scalar_mul_sourceNorm, adelicHeight_eq_scalar_mul_sourceNorm] at h
      have h' : s * adelicSourceNorm F G rho (g * t) ≤ s * (adelicSourceNorm F G rho g * B) := by
        simpa only [s, mul_assoc] using h
      exact (le_of_mul_le_mul_left h' hs).trans_eq (mul_comm _ _)
    refine ⟨1 + Real.log B, le_add_of_nonneg_right (Real.log_nonneg hB), fun y => ?_⟩
    let f (r : Γ) := adelicSourceNorm F G rho (r.val * y.out)
    let f' (r : Γ) := adelicSourceNorm F G rho (r.val * (y.out * t))
    have hBelow : BddBelow (range f') :=
      ⟨0, forall_mem_range.2 fun r => (adelicSourceNorm_pos F G rho hN (r.val * (y.out * t))).le⟩
    have hinf : (⨅ r, f' r) ≤ B * (⨅ r, f r) := by
      rw [mul_comm B, ← div_le_iff₀ hBpos]
      refine le_ciInf fun r => (div_le_iff₀ hBpos).2 ?_
      rw [mul_comm (f r)]
      exact (ciInf_le hBelow r).trans (by simpa only [f, f', mul_assoc] using hmul (r.val * y.out))
    have hmax : max 1 (⨅ r, f' r) ≤ B * max 1 (⨅ r, f r) :=
      max_le (one_le_mul_of_one_le_of_one_le hB (le_max_left _ _))
        (hinf.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hBpos.le))
    have hlog := Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) hmax
    rw [Real.log_mul hBpos.ne' (zero_lt_one.trans_le (le_max_left _ _)).ne'] at hlog
    have hright : LeftCosetSpace.rightTranslate Γ t y = LeftCosetSpace.mk Γ (y.out * t) := by
      conv_lhs => rw [← Quotient.out_eq y]
      rfl
    rw [hright, rationalLogHeight_mk_eq]
    change 1 + Real.log (max 1 (⨅ r, f' r)) ≤ (1 + Real.log B) * (1 + Real.log (max 1 (⨅ r, f r)))
    nlinarith [Real.log_nonneg hB, Real.log_nonneg (le_max_left (1 : ℝ) (⨅ r, f r))]

end Height

/-- Infinite right translation preserves the logarithmically weighted automorphic condition
and carries the compact-finiteness condition to the conjugate compact. -/
def LogSquareIntegrableCompactTranslationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (Φ : AdelicGroupPoints F G → ℂ)
    (a : InfiniteAdelicGroupPoints F G),
    IsConnectedReductive G → IsMaximalCompactSubgroup F G K →
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    IsLogSquareIntegrableAutomorphicForm F G (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom)
      rho hsmooth hcalc (fun g => Φ (g * ofInfinite F G a))

theorem logSquareIntegrableCompactTranslation : LogSquareIntegrableCompactTranslationStatement := by
  intro F _ _ G _ _ _ K N d rho hsmooth hcalc Φ a hG hK hΦ
  obtain ⟨hauto, ⟨ν, hν⟩, m, hLp⟩ := hΦ
  let t := ofInfinite F G a
  let K' := K.map (MulAut.conj t).toMonoidHom
  have hK' := hK.map_conj t
  have hinf : K'.comap (ofInfinite F G).toMonoidHom =
      (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [hK'.comap_ofInfinite_eq_map_infinite, hK.comap_ofInfinite_eq_map_infinite]
    exact map_infinite_map_conj_ofInfinite K a
  refine ⟨hinf.symm ▸ hauto.infiniteRightTranslate hcalc a, ⟨ν, ?_⟩, ⟨m, ?_⟩⟩
  · intro z hz g
    change Φ ((z * g) * t) = parameterPower F G (imaginaryParameter F G ν) z * Φ (g * t)
    rw [mul_assoc, hν z hz]
  let Γ := rationalSubgroup F G
  let σ := rationalLogHeight F G rho
  let q := LeftCosetSpace.rightTranslate Γ t
  let μQ := rationalQuotientHaarMeasure F G
  let := adelicHaarUnimodularity.2 F G hG
  have hq : MeasurePreserving q μQ μQ := measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G t
  have hbase := hLp.comp_measurePreserving hq
  obtain ⟨C, _, hbound⟩ := exists_rationalLogHeight_rightTranslate_le rho t
  let w (y : RationalQuotient F G) : ℂ := ((σ (q y) / σ y) ^ m : ℝ)
  have hw : Measurable w := Complex.measurable_ofReal.comp
    ((((measurable_rationalLogHeight rho).comp hq.measurable).div
      (measurable_rationalLogHeight rho)).pow_const m)
  have hpos (y : RationalQuotient F G) : 0 < σ y := zero_lt_one.trans_le (one_le_rationalLogHeight rho y)
  have hprod : MemLp (fun y => w y * (Φ (q y).out / (σ (q y) : ℂ) ^ m)) 2 μQ := by
    apply (hbase.norm.const_mul (C ^ m)).mono' (hw.aestronglyMeasurable.mul hbase.aestronglyMeasurable)
    filter_upwards with y
    change ‖w y * (Φ (q y).out / (σ (q y) : ℂ) ^ m)‖ ≤ C ^ m * ‖Φ (q y).out / (σ (q y) : ℂ) ^ m‖
    rw [norm_mul]
    have hwC : ‖w y‖ ≤ C ^ m := by
      have hratio : 0 ≤ σ (q y) / σ y := div_nonneg (hpos _).le (hpos _).le
      change ‖(((σ (q y) / σ y) ^ m : ℝ) : ℂ)‖ ≤ C ^ m
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hratio _)]
      exact pow_le_pow_left₀ hratio ((div_le_iff₀ (hpos y)).2 (hbound y)) _
    exact mul_le_mul_of_nonneg_right hwC (norm_nonneg _)
  change MemLp (fun y : RationalQuotient F G => Φ (y.out * t) / (σ y : ℂ) ^ m) 2 μQ
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun y => ?_) hprod
  have hout : Φ (q y).out = Φ (y.out * t) := by
    rw [show q y = LeftCosetSpace.mk Γ (y.out * t) from rationalQuotient_rightTranslate_eq_mk_out_mul t y]
    exact leftInvariant_mk_out hauto.1 (y.out * t)
  change (((σ (q y) / σ y) ^ m : ℝ) : ℂ) * (Φ (q y).out / (σ (q y) : ℂ) ^ m) =
    Φ (y.out * t) / (σ y : ℂ) ^ m
  rw [hout, Complex.ofReal_pow, Complex.ofReal_div, div_pow]
  field_simp [Complex.ofReal_ne_zero.mpr (hpos y).ne', Complex.ofReal_ne_zero.mpr (hpos (q y)).ne']

end Langlands.Global
