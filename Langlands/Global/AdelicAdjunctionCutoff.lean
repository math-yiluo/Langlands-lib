import Langlands.Global.AdelicAdjunctionNormalizedKernel
import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.Global.AdelicInducedInnerProductGramCoordinateProof

/-! # Integration in the positive split-component variable -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global

private theorem integrable_integral_shiftedCutoff {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (μA : Measure A) (ν : Measure Z) [SFinite μA] [SFinite ν] {n : ℕ}
    (y : A → (Fin n → ℝ)) (c : ℝ≥0)
    (hy : MeasurePreserving y μA (c • (volume : Measure (Fin n → ℝ))))
    (β : (Fin n → ℝ) → ℝ) (hβc : Continuous β) (hβs : HasCompactSupport β) (hβ : ∫ t, β t = 1)
    (s : Z → (Fin n → ℝ)) (hs : Measurable s) (J : Z → ℂ) (hJ : Measurable J) (hJi : Integrable J ν) :
    let g : A × Z → ℂ := fun z => (β (y z.1 + s z.2) : ℂ) * J z.2
    Integrable g (μA.prod ν) ∧ (∫ z, g z ∂(μA.prod ν)) = (c : ℝ) * ∫ z, J z ∂ν := by
  intro g
  have hg : Measurable g := (Complex.continuous_ofReal.measurable.comp (hβc.measurable.comp
    ((hy.measurable.comp measurable_fst).add (hs.comp measurable_snd)))).mul (hJ.comp measurable_snd)
  let B := (c : ℝ≥0∞) * ∫⁻ u, ‖(β u : ℂ)‖ₑ
  have hβi : Integrable β volume := hβc.integrable_of_hasCompactSupport hβs
  have hB : B < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (by
    simp_rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
    exact hasFiniteIntegral_iff_enorm.mp hβi.hasFiniteIntegral)
  have htrans (u : Fin n → ℝ) : MeasurePreserving (fun a => y a + u) μA (c • volume) :=
    ((measurePreserving_add_right volume u).smul_measure c).comp hy
  have hn (z : Z) : (∫⁻ a, ‖g (a, z)‖ₑ ∂μA) = B * ‖J z‖ₑ := by
    simp only [g, enorm_mul]
    have hF : Measurable (fun t => ‖(β t : ℂ)‖ₑ) :=
      (Complex.continuous_ofReal.measurable.comp hβc.measurable).enorm
    have hF' : Measurable (fun a => ‖(β (y a + s z) : ℂ)‖ₑ) := hF.comp (htrans (s z)).measurable
    rw [lintegral_mul_const _ hF', ← lintegral_map hF (htrans (s z)).measurable,
      (htrans (s z)).map_eq, lintegral_smul_measure]
    rfl
  have hgi : Integrable g (μA.prod ν) := by
    refine ⟨hg.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    rw [lintegral_prod_symm _ hg.enorm.aemeasurable]
    simp_rw [hn]
    rw [lintegral_const_mul _ hJ.enorm]
    exact ENNReal.mul_lt_top hB (hasFiniteIntegral_iff_enorm.mp hJi.hasFiniteIntegral)
  refine ⟨hgi, ?_⟩
  rw [integral_prod_symm _ hgi, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only [g]
  rw [integral_mul_const, integral_complex_ofReal, ← integral_map (htrans (s z)).aemeasurable
    hβc.measurable.aestronglyMeasurable, (htrans (s z)).map_eq, integral_smul_nnreal_measure, hβ]
  simp [NNReal.smul_def]

private theorem measurePreserving_cutoffProduct {A X Y N : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace N]
    (μA : Measure A) (μX : Measure X) (μY : Measure Y) (μN : Measure N)
    [SFinite μA] [SFinite μX] [SFinite μY] [SFinite μN] :
    MeasurePreserving (fun z : A × (X × (Y × N)) => ((z.2.1, (z.1, z.2.2.2)), z.2.2.1))
      (μA.prod (μX.prod (μY.prod μN))) ((μX.prod (μA.prod μN)).prod μY) := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μA μX (μY.prod μN))
  have h₂ := (Measure.measurePreserving_swap (μ := μA) (ν := μX)).prod (MeasurePreserving.id (μY.prod μN))
  have h₃ := measurePreserving_prodAssoc μX μA (μY.prod μN)
  have h₄ := (MeasurePreserving.id μX).prod ((MeasurePreserving.id μA).prod
    (Measure.measurePreserving_swap (μ := μY) (ν := μN)))
  have h₅ := (MeasurePreserving.id μX).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μA μN μY))
  have h₆ := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μX (μA.prod μN) μY)
  exact h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))))

end Langlands.Global

namespace Langlands.Global.InducedInnerProductGram

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus LeftCosetSpace
open RestrictionSplitCentre
open scoped CategoryTheory.MonObj

variable {F : Type} [Field F] [NumberField F]
  {P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)

local notation "Mₐ" => (AdelicGroupPoints F M)
local notation "Γ" => (AdelicGroupPoints.rationalSubgroup F M)
local notation "C" => (canonicalRationalSubgroup F M)
local notation "D" => (fundamentalDomain Γ (isDiscrete_rationalSubgroup F M))
local notation "N" => (NormOneRationalQuotient F M)
local notation "μN" => (normOneRationalQuotientHaarMeasure F M)
local notation "Qm" => (RationalQuotient F M)
local notation "μQ" => (rationalQuotientHaarMeasure F M)

private theorem rational_le_canonical : Γ ≤ C :=
  principal_le_rationalSubgroup F M (canonicalRestrictionTorus F M) (canonicalRestrictionComponent F M)

/-- The positive cutoff applied to the target Levi logarithm plus a measurable shift. -/
def cutoffWeightedKernel {X Y : Type*} (J : X × (Y × CanonicalQuotient F M) → ℂ)
    (β : (Fin n → ℝ) → ℝ) (s : X → (Fin n → ℝ)) (z : (X × Mₐ) × Y) : ℂ :=
  (β (parameterCoordinates F P e (characterLog F P (map F M P l z.1.2)) + s z.1.1) : ℂ) *
    J (z.1.1, z.2, mk C z.1.2)

set_option maxHeartbeats 1500000 in
/-- Integrating any translated unit-integral cutoff on the target Levi gives the same
scalar times the integral of the kernel on the canonical quotient. -/
theorem integrate_cutoffWeightedKernel (hM : IsConnectedReductive M) (hl : IsRationalLeviSubgroup l)
    (μM : Measure Mₐ) [μM.IsHaarMeasure] {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μX : Measure X) (μY : Measure Y) [SFinite μX] [SFinite μY]
    (J : X × (Y × CanonicalQuotient F M) → ℂ) (hJ : Measurable J)
    (hJi : Integrable J (μX.prod (μY.prod (canonicalMeasure F M)))) :
    ∃ d : ℝ, ∀ (β : (Fin n → ℝ) → ℝ), Continuous β → HasCompactSupport β → (∫ u, β u = 1) →
      ∀ (s : X → (Fin n → ℝ)), Measurable s →
        let f := cutoffWeightedKernel l e J β s
        let ν := (μX.prod (μM.restrict D)).prod μY
        Measurable f ∧ Integrable f ν ∧
          (∫ z, f z ∂ν) = (d : ℂ) * ∫ z, J z ∂(μX.prod (μY.prod (canonicalMeasure F M))) := by
  let T := canonicalTorus F M
  let i := canonicalComponent F M
  have hi := canonical_characterRestrict_injective F M centralSplitTorusCharacter hM
  let := canonical_finiteIndex F M hM
  have hsc := isSplitComponent_canonicalComponent F M
  obtain ⟨I, hI, ⟨e₀⟩⟩ := hsc.1.1.1
  let := Fintype.ofFinite I
  have hc : IsCentral i := hsc.1.2
  let A := intrinsicSubgroup F T
  let μA := normalizedPositiveHaarMeasure F M T i hi I e₀ hc
  let := positiveIsTopologicalGroup F T I e₀
  let : μA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e₀ hc
  let : SigmaFinite μA := normalizedPositiveHaarMeasure_sigmaFinite F M T i hi I e₀ hc
  let y := torusCoordinateHomeomorph l e T i hi I e₀ hl
  let yM (m : Mₐ) := parameterCoordinates F P e (characterLog F P (map F M P l m))
  have hyM : Continuous yM := (InducedInnerProductSesquilinear.continuous_parameterCoordinates F P e).comp
    ((continuous_characterLog F P).comp (map F M P l).continuous)
  let yQ (m : Qm) := yM m.out
  have hyInv (g : Mₐ) (hg : g ∈ Γ) (m : Mₐ) : yM (g * m) = yM m := by
    unfold yM
    rw [InducedInnerProductSesquilinear.characterLog_map_normOne_mul l (rationalSubgroup_le_normOneSubgroup F M hg)]
  have hyQ : Measurable yQ := measurable_out_of_invariant Γ hyM.measurable hyInv
  let cQ (m : Qm) := mk C m.out
  have hcInv (g : Mₐ) (hg : g ∈ Γ) (m : Mₐ) : mk C (g * m) = mk C m :=
    mk_subgroup_mul C ⟨g, rational_le_canonical hg⟩ m
  have hcQ : Measurable cQ := measurable_out_of_invariant Γ (measurable_mk C) hcInv
  let μ₀ : Measure Mₐ := Measure.haar
  let dM := Measure.haarScalarFactor μM μ₀
  let : (Measure.map y μA).IsAddHaarMeasure :=
    isAddHaarMeasure_map_of_map_mul μA y (torusCoordinateHomeomorph_mul l e T i hi I e₀ hl)
  let dA := Measure.addHaarScalarFactor (Measure.map y μA) (volume : Measure (Fin n → ℝ))
  have hy : MeasurePreserving y μA (dA • (volume : Measure (Fin n → ℝ))) :=
    ⟨y.continuous.measurable, Measure.isAddLeftInvariant_eq_smul (Measure.map y μA) volume⟩
  let L := rationalQuotientDecomposition F M T i hi I e₀ hc
  have hL : MeasurePreserving L (μA.prod μN) μQ := measurePreserving_rationalQuotientDecomposition F M T i hi I e₀ hc
  let jN := normOneToQuotient F M (canonicalRestrictionTorus F M) (canonicalRestrictionComponent F M)
  have hjN : MeasurePreserving jN μN (canonicalMeasure F M) := ⟨measurable_normOneToQuotient _ _ _ _, rfl⟩
  have hL_y (a : A) (b : N) : yQ (L (a, b)) = y a := by
    obtain ⟨m, rfl⟩ := mk_surjective (rationalNormOneSubgroup F M) b
    rw [show L (a, mk (rationalNormOneSubgroup F M) m) = mk Γ (positivePointMap F M T i a * m) from
      rationalQuotientDecomposition_mk F M T i hi I e₀ hc a m]
    change yM (mk Γ (positivePointMap F M T i a * m)).out = y a
    rw [out_mk_of_invariant Γ yM hyInv]
    unfold yM
    rw [InducedInnerProductSesquilinear.characterLog_map_mul_normOne l m.property]
    exact (torusCoordinateHomeomorph_apply l e T i hi I e₀ hl a).symm
  have hL_c (a : A) (b : N) : cQ (L (a, b)) = jN b := by
    obtain ⟨m, rfl⟩ := mk_surjective (rationalNormOneSubgroup F M) b
    rw [show L (a, mk (rationalNormOneSubgroup F M) m) = mk Γ (positivePointMap F M T i a * m) from
      rationalQuotientDecomposition_mk F M T i hi I e₀ hc a m]
    change mk C (mk Γ (positivePointMap F M T i a * m)).out = mk C m.val
    rw [out_mk_of_invariant Γ (mk C) hcInv]
    have ha₀ : positivePointMap F M T i a ∈ canonicalSubgroup F M := by
      rw [canonicalSubgroup_eq_imageSubgroup F M]
      exact ⟨a.val, a.property, rfl⟩
    have ha : positivePointMap F M T i a ∈ C := Subgroup.mem_sup_left ha₀
    exact mk_subgroup_mul C ⟨_, ha⟩ m.val
  let νQ := (μX.prod μQ).prod μY
  have hq : MeasurePreserving (mk Γ) (μM.restrict D) (dM • μQ) := by
    have hq₀ : MeasurePreserving (mk Γ) (μ₀.restrict D) μQ := by
      refine ⟨measurable_mk Γ, ?_⟩
      exact (rationalQuotientHaarMeasure_eq F M (isFundamentalDomain Γ (isDiscrete_rationalSubgroup F M) μ₀)).symm
    have hm : μM = dM • μ₀ := Measure.isMulLeftInvariant_eq_smul μM μ₀
    rw [hm, Measure.restrict_smul]
    exact hq₀.smul_measure dM
  let t : (X × Mₐ) × Y → (X × Qm) × Y := Prod.map (Prod.map id (mk Γ)) id
  have ht : MeasurePreserving t ((μX.prod (μM.restrict D)).prod μY) (dM • νQ) := by
    have h := ((MeasurePreserving.id μX).prod hq).prod (MeasurePreserving.id μY)
    change MeasurePreserving t _ _ at h
    simpa only [Measure.prod_smul_right, Measure.prod_smul_left, νQ] using h
  let θ : A × (X × (Y × N)) → (X × Qm) × Y := fun z => ((z.2.1, L (z.1, z.2.2.2)), z.2.2.1)
  have hθ : MeasurePreserving θ (μA.prod (μX.prod (μY.prod μN))) νQ :=
    (((MeasurePreserving.id μX).prod hL).prod (MeasurePreserving.id μY)).comp
      (measurePreserving_cutoffProduct μA μX μY μN)
  let j : X × (Y × N) → X × (Y × CanonicalQuotient F M) := Prod.map id (Prod.map id jN)
  have hj : MeasurePreserving j (μX.prod (μY.prod μN)) (μX.prod (μY.prod (canonicalMeasure F M))) :=
    (MeasurePreserving.id μX).prod ((MeasurePreserving.id μY).prod hjN)
  refine ⟨(dM : ℝ) * (dA : ℝ), fun β hβc hβs hβ s hs => ?_⟩
  let fQ : (X × Qm) × Y → ℂ := fun z => (β (yQ z.1.2 + s z.1.1) : ℂ) * J (z.1.1, z.2, cQ z.1.2)
  have hfQ : Measurable fQ := (Complex.continuous_ofReal.measurable.comp (hβc.measurable.comp
    ((hyQ.comp (measurable_snd.comp measurable_fst)).add (hs.comp (measurable_fst.comp measurable_fst))))).mul
    (hJ.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (hcQ.comp (measurable_snd.comp measurable_fst)))))
  have hf (z : (X × Mₐ) × Y) : fQ (t z) = cutoffWeightedKernel l e J β s z := by
    change (β (yM (mk Γ z.1.2).out + s z.1.1) : ℂ) * J (z.1.1, z.2, mk C (mk Γ z.1.2).out) = _
    rw [out_mk_of_invariant Γ yM hyInv, out_mk_of_invariant Γ (mk C) hcInv]
    rfl
  have hθF : fQ ∘ θ = fun z => (β (y z.1 + (s ∘ Prod.fst) z.2) : ℂ) * (J ∘ j) z.2 := by
    funext z
    change (β (yQ (L (z.1, z.2.2.2)) + s z.2.1) : ℂ) * J (z.2.1, z.2.2.1, cQ (L (z.1, z.2.2.2))) = _
    rw [hL_y, hL_c]
    rfl
  have h := integrable_integral_shiftedCutoff μA (μX.prod (μY.prod μN)) y dA hy β hβc hβs hβ
    (s ∘ Prod.fst) (hs.comp measurable_fst) (J ∘ j) (hJ.comp hj.measurable)
    (hj.integrable_comp_of_integrable hJi)
  have hQi : Integrable fQ νQ := (hθ.integrable_comp hfQ.aestronglyMeasurable).mp (hθF.symm ▸ h.1)
  have hQi' : Integrable fQ (dM • νQ) := hQi.smul_measure_nnreal
  have hfEq : cutoffWeightedKernel l e J β s = fQ ∘ t := (funext hf).symm
  refine ⟨hfEq ▸ ?_, ?_⟩
  · exact hfQ.comp ht.measurable
  · rw [hfEq]
    refine ⟨ht.integrable_comp_of_integrable hQi', ?_⟩
    change (∫ x, fQ (t x) ∂((μX.prod (μM.restrict D)).prod μY)) = _
    rw [← integral_map ht.aemeasurable hfQ.aestronglyMeasurable, ht.map_eq, integral_smul_nnreal_measure,
      ← hθ.map_eq, integral_map hθ.aemeasurable hfQ.aestronglyMeasurable]
    rw [show (fun x => fQ (θ x)) = fQ ∘ θ from rfl, hθF, h.2]
    change (dM • ((dA : ℝ) * ∫ x, J (j x) ∂(μX.prod (μY.prod μN))) : ℂ) = _
    rw [← integral_map hj.aemeasurable hJ.aestronglyMeasurable, hj.map_eq]
    simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

end Langlands.Global.InducedInnerProductGram
