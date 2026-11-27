import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof
import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.Global.AdelicInducedInnerProductIntegrable

/-! # Integrability from simple-root logarithms on a fixed norm-one Siegel chart -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators ENNReal NNReal Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Langlands.Global.AdelicSiegelFactors

open GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (j : T₀ ⟶ T)

local notation "A" => AdelicGroupPoints F G
local notation "A₁" => normOneSubgroup F G
local notation "Q₁" => NormOneRationalQuotient F G
local notation "Q" => RationalQuotient F G
local notation "μ₁" => normOneRationalQuotientHaarMeasure F G
local notation "μQ" => rationalQuotientHaarMeasure F G
local notation "Δ" => simpleRelativeRoots i ν
local notation "Torus" => intrinsicSubgroup F T₀
local notation "CompactChart" =>
  CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)
local notation "nG" => map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
local notation "mG" => map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)
local notation "aG" => positiveMap F G T i T₀ j
local notation "chamber" => weakSimpleRootChamber F T₀ T j G i ν

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- One plus the sum of the absolute simple-root logarithms on the positive Siegel torus. -/
def siegelRootLogSize (a : Torus) : ℝ :=
  1 + ∑ᶠ α : Δ, |characterLog F T₀.toGrp a.val (j ≫ α.val)|

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem one_le_siegelRootLogSize (a : Torus) : 1 ≤ siegelRootLogSize i ν j a :=
  le_add_of_nonneg_right (finsum_nonneg fun _ => abs_nonneg _)

local notation "σ" => siegelRootLogSize i ν j

/-- On a fixed algebraic Siegel setup, a uniform multiple of the minimal modulus
times a sufficiently large inverse power of the simple-root logarithmic size is
an integrable majorant on the norm-one quotient. -/
theorem exists_normOneSiegelIntegralBound (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ∃ (C : CompactChart) (t : ℝ≥0ˣ) (W : Set A) (d : ℕ) (L : ℝ≥0∞),
      W.Finite ∧ W ⊆ A₁ ∧ L < ∞ ∧
      ∀ (f : A → ℝ≥0∞), Measurable f →
      (∀ q ∈ rationalSubgroup F G, ∀ g : A, f (q * g) = f g) →
      ∀ B : ℝ≥0∞,
      (∀ a ∈ chamber t, ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
        f (nG n * mG m * aG a * k * w) ≤
          B * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) *
            ENNReal.ofReal ((σ a)⁻¹ ^ d)) →
      ∫⁻ q : Q₁, f q.out.val ∂μ₁ ≤ B * L := by
  classical
  obtain ⟨K, H₁, W, hKc, hH₁, hKH₁, hH₁P, hcompat, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F G hG T i ν T₀ j hsetup
  obtain ⟨C, t, rfl, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F G hG T i ν T₀ j hsetup K hKc W hW hW1 hcov
  obtain ⟨hTmax, -, -, -, -, -, -, -, Z₀, zc, hzsplit, -⟩ := id hsetup
  let z := CommGroupScheme.groupHom zc ≫ i
  have hzc : IsCentral z := hzsplit.1.2
  have hZ : IsSplitTorus Z₀.toGrp := hzsplit.1.1.1
  obtain ⟨I, hI, ⟨e⟩⟩ := id hZ
  let : Fintype I := Fintype.ofFinite I
  let : (characterRestrict z).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG Z₀ z hzsplit
  have hzinj : Function.Injective (characterRestrict z) :=
    characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hzsplit
  obtain ⟨m₀, hm₀, hχ⟩ := RepresentationGrowth.exists_characterNorm_full F Z₀ z e
  choose χ hχ using hχ
  let : Fintype Δ := (hTmax.1.1.finite_simpleRelativeRoots i ν).fintype
  let Λ := I ⊕ Δ
  let coords := siegelCoordinates (i := i) (ν := ν) (j := j) zc χ
  have hbox := isCompact_dyadicBox_siegelCoordinates zc hG hsetup e χ
    (Nat.mul_pos hm₀ Module.finrank_pos) hχ
  obtain ⟨eδ, heδ⟩ := exists_siegelModulusNN_le zc hsetup χ
  obtain ⟨D, hD, hDb⟩ := exists_lintegral_centralSiegelSet_le zc hzc hG hsetup C t H₁ hH₁ hKH₁ hH₁P
    hcompat _ hbox eδ heδ
  let Zp := intrinsicSubgroup F Z₀
  let μz := normalizedPositiveHaarMeasure F G Z₀ z hzinj I e hzc
  let : LocallyCompactSpace Zp := positiveLocallyCompactSpace F Z₀ I e
  let : T2Space Zp := (positiveLogCoordinateEquiv F Z₀ I e).toHomeomorph.symm.t2Space
  let : μz.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G Z₀ z hzinj I e hzc
  let : SigmaFinite μz := normalizedPositiveHaarMeasure_sigmaFinite F G Z₀ z hzinj I e hzc
  let : IsFiniteMeasure μ₁ := isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F G hG
  obtain ⟨S, hSc, hSn⟩ := exists_compact_mem_nhds (1 : Zp)
  have hSmeas : MeasurableSet S := hSc.isClosed.measurableSet
  have hS0 : μz S ≠ 0 := (μz.measure_pos_of_mem_nhds hSn).ne'
  have hSfin : μz S < ∞ := hSc.measure_lt_top
  let zG := positiveMap F G T i Z₀ zc
  let centreLogSize (a : Zp) : ℝ := ∑ c : I, |characterLog F G (zG a) (χ c)|
  have hcentre : Continuous centreLogSize :=
    continuous_finsetSum _ fun c _ => ((continuous_characterLog_eval F G (χ c)).comp zG.continuous).abs
  obtain ⟨E, hE⟩ := (hSc.image hcentre).bddAbove
  let nι := Fintype.card Λ
  let d := 2 * nι
  let c₀ := Real.log 2
  let C₀ := E + nι * c₀
  have hc₀ : 0 < c₀ := Real.log_pos (by norm_num)
  let Φ : (Λ → ℤ) → ℝ≥0∞ := fun κ =>
    ENNReal.ofReal ((max 1 (c₀ * ∑ c, |(κ c : ℝ)| - C₀))⁻¹ ^ d)
  have hΦ : ∑' κ, Φ κ ≠ ∞ := SiegelSetMeasure.tsum_decay_ne_top hc₀ C₀
  have hMajorant (p : Zp × Torus) (hp : p.1 ∈ S) :
      ENNReal.ofReal ((σ p.2)⁻¹ ^ d) ≤ Φ (SiegelSetMeasure.zIndex coords p) := by
    have hcLog (c : Λ) :
        |(SiegelSetMeasure.zIndex coords p c : ℝ)| * c₀ ≤
          |Real.log (((coords c p : ℝ≥0ˣ) : ℝ≥0) : ℝ)| + c₀ := by
      have hp0 : 0 < (coords c p : ℝ≥0) := pos_iff_ne_zero.mpr (coords c p).ne_zero
      calc
        _ ≤ (|Real.log (((coords c p : ℝ≥0ˣ) : ℝ≥0) : ℝ)| / c₀ + 1) * c₀ :=
          mul_le_mul_of_nonneg_right (abs_intLog_two_le hp0) hc₀.le
        _ = _ := by rw [add_mul, div_mul_cancel₀ _ hc₀.ne', one_mul]
    have hsum : c₀ * ∑ c : Λ, |(SiegelSetMeasure.zIndex coords p c : ℝ)| ≤
        centreLogSize p.1 + (σ p.2 - 1) + nι * c₀ := by
      rw [mul_comm, Finset.sum_mul]
      refine (Finset.sum_le_sum fun c _ => hcLog c).trans_eq ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.sum_sum_type]
      change centreLogSize p.1 +
        (∑ α : Δ, |characterLog F T₀.toGrp p.2.val (j ≫ α.val)|) + nι * c₀ = _
      rw [siegelRootLogSize, finsum_eq_sum_of_fintype]
      ring
    have hmax : max 1 (c₀ * ∑ c : Λ, |(SiegelSetMeasure.zIndex coords p c : ℝ)| - C₀) ≤ σ p.2 := by
      apply max_le (one_le_siegelRootLogSize i ν j p.2)
      have hEp : centreLogSize p.1 ≤ E := hE ⟨p.1, hp, rfl⟩
      dsimp only [C₀]
      linarith
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (inv_nonneg.mpr (zero_le_one.trans (one_le_siegelRootLogSize i ν j p.2)))
      (inv_anti₀ (one_pos.trans_le (le_max_left _ _)) hmax) _
  let L₀ : ℝ≥0∞ := ∑' _w : W, D * ∑' κ, Φ κ
  have hL₀ : L₀ < ∞ := by
    let : Fintype W := hW.fintype
    dsimp only [L₀]
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top hD.lt_top hΦ.lt_top)
  refine ⟨C, t, W, d, L₀ * (μz S)⁻¹, hW, hW1,
    ENNReal.mul_lt_top hL₀ (by simpa only [ENNReal.inv_lt_top] using pos_iff_ne_zero.mpr hS0), ?_⟩
  intro f hf hinv B hbound
  let cut : Zp → ℝ≥0∞ := S.indicator 1
  have hcut : Measurable cut := measurable_const.indicator hSmeas
  let π := normOneProjection F G Z₀ z hzinj I e hzc
  let zpart := positiveFactor F G Z₀ z hzinj I e
  let lift (x : A) : ℝ≥0∞ := cut (zpart x) * f (π x).val
  have hlift : Measurable lift :=
    (hcut.comp zpart.continuous.measurable).mul (hf.comp (continuous_subtype_val.comp π.continuous).measurable)
  have hlift_mul (a : Zp) (x : A₁) : lift (zG a * x.val) = cut a * f x.val := by
    change cut (zpart (positivePointMap F G Z₀ z a * x.val)) *
      f (π (positivePointMap F G Z₀ z a * x.val)).val = _
    simp only [zpart, π, map_mul, positiveFactor_positivePointMap, positiveFactor_normOne,
      normOneProjection_positivePointMap, normOneProjection_normOne, one_mul, mul_one]
  have hlift_inv (q : A) (hq : q ∈ rationalSubgroup F G) (x : A) :
      lift (q * x) = lift x := by
    let q₁ : A₁ := ⟨q, rationalSubgroup_le_normOneSubgroup F G hq⟩
    change cut (zpart (q₁.val * x)) * f (π (q₁.val * x)).val = _
    simp only [zpart, π, map_mul, positiveFactor_normOne, normOneProjection_normOne, one_mul,
      Subgroup.coe_mul, lift]
    change cut (zpart x) * f (q * (π x).val) = cut (zpart x) * f (π x).val
    rw [hinv q hq]
  have hwb (w : W) : ∫⁻ y in centralSiegelSet (j := j) zc hzc C t, lift (y * w.val) ∂Measure.haar ≤
      B * (D * ∑' κ, Φ κ) := by
    refine (hDb (fun y => lift (y * w.val)) (hlift.comp (continuous_id.mul continuous_const).measurable)
      (fun κ => B * Φ κ) ?_).trans_eq ?_
    · intro p hp n hn m hm k hk
      let v := nG n * mG m * aG p.2 * k * w.val
      have hV : v ∈ A₁ := by
        apply (normOneSubgroup F G).mul_mem _ (hW1 w.property)
        apply hsetup.weakSiegelProduct_subset_normOne F G T i ν T₀ j C t
        exact (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j _ _).mpr
          ⟨n, hn, m, hm, p.2, hp, k, hk, rfl⟩
      have hX : nG n * mG m * siegelTorusMap (j := j) zc hzc p * k * w.val = zG p.1 * v := by
        rw [siegelTorusMap_apply, ← mul_assoc,
          ← (positiveMap_central zc hzc p.1 (nG n * mG m)).eq]
        simp only [v, zG, mul_assoc]
      rw [hX, hlift_mul p.1 ⟨v, hV⟩]
      by_cases hS : p.1 ∈ S
      · rw [show cut p.1 = 1 from Set.indicator_of_mem hS _, one_mul]
        calc
          f v ≤ B * (siegelModulusNN (i := i) (ν := ν) (j := j) p.2 : ℝ≥0∞) *
              ENNReal.ofReal ((σ p.2)⁻¹ ^ d) := hbound p.2 hp n hn m hm k hk w.val w.property
          _ ≤ B * (siegelModulusNN (i := i) (ν := ν) (j := j) p.2 : ℝ≥0∞) *
              Φ (SiegelSetMeasure.zIndex coords p) := by gcongr; exact hMajorant p hS
          _ = _ := by ac_rfl
      · simp only [cut, Set.indicator_of_notMem hS, zero_mul, zero_le]
    · rw [ENNReal.tsum_mul_left]
      ac_rfl
  have hcov' := exists_rational_mul_mem_centralSiegelSet_mul zc hzc hG hzsplit C t W hcover
  let : (Measure.haar : Measure A).IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  let : Finite W := hW.to_subtype
  have hFull : ∫⁻ q : Q, lift q.out ∂μQ ≤ B * L₀ := calc
    _ ≤ ∫⁻ x in centralSiegelSet (j := j) zc hzc C t * W, lift x ∂Measure.haar :=
      LeftCosetSpace.lintegral_comp_out_le_setLIntegral _ _ _ hlift hlift_inv hcov'
    _ ≤ ∑' w : W, ∫⁻ x in (fun x => x * w.val⁻¹) ⁻¹'
          centralSiegelSet (j := j) zc hzc C t, lift x ∂Measure.haar := by
      refine (lintegral_mono_set ?_).trans (lintegral_iUnion_le _ _)
      rintro _ ⟨s, hs, w, hw, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, by simpa only [Set.mem_preimage, mul_inv_cancel_right] using hs⟩
    _ = ∑' w : W, ∫⁻ y in centralSiegelSet (j := j) zc hzc C t, lift (y * w.val) ∂Measure.haar := by
      refine tsum_congr fun w => ?_
      have hmp := measurePreserving_mul_right (Measure.haar : Measure A) w.val⁻¹
      have h := hmp.setLIntegral_comp_preimage_emb
        (MeasurableEquiv.mulRight w.val⁻¹).measurableEmbedding
        (fun y => lift (y * w.val)) (centralSiegelSet (j := j) zc hzc C t)
      simpa only [inv_mul_cancel_right] using h
    _ ≤ ∑' _w : W, B * (D * ∑' κ, Φ κ) := ENNReal.tsum_le_tsum hwb
    _ = B * L₀ := ENNReal.tsum_mul_left
  let Ξ := rationalQuotientDecomposition F G Z₀ z hzinj I e hzc
  have hΞ := measurePreserving_rationalQuotientDecomposition F G Z₀ z hzinj I e hzc
  have hQ : Measurable (fun q : Q => lift q.out) :=
    LeftCosetSpace.measurable_out_of_invariant (rationalSubgroup F G) hlift hlift_inv
  have hinv₁ (q : A₁) (hq : q ∈ rationalNormOneSubgroup F G) (x : A₁) :
      f (q * x).val = f x.val :=
    hinv q.val (rationalNormOneSubgroupInclusion F G ⟨q, hq⟩).property x.val
  have hQ₁ : Measurable (fun q : Q₁ => f q.out.val) :=
    LeftCosetSpace.measurable_out_of_invariant (rationalNormOneSubgroup F G)
      (hf.comp continuous_subtype_val.measurable) hinv₁
  have hEq (p : Zp × Q₁) : lift (Ξ p).out = cut p.1 * f p.2.out.val := by
    obtain ⟨a, q⟩ := p
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F G) q
    rw [show Ξ (a, LeftCosetSpace.mk (rationalNormOneSubgroup F G) x) =
        LeftCosetSpace.mk (rationalSubgroup F G) (zG a * x.val) from
      rationalQuotientDecomposition_mk F G Z₀ z hzinj I e hzc a x,
      LeftCosetSpace.out_mk_of_invariant (rationalSubgroup F G) lift hlift_inv,
      hlift_mul a x,
      LeftCosetSpace.out_mk_of_invariant (rationalNormOneSubgroup F G) (fun x => f x.val) hinv₁]
  have hFold : μz S * (∫⁻ q : Q₁, f q.out.val ∂μ₁) = ∫⁻ q : Q, lift q.out ∂μQ := by
    rw [← hΞ.lintegral_comp hQ]
    have hProd := lintegral_prod_mul (hcut.aemeasurable : AEMeasurable cut μz)
      (hQ₁.aemeasurable : AEMeasurable (fun q : Q₁ => f q.out.val) μ₁)
    change (∫⁻ p : Zp × Q₁, cut p.1 * f p.2.out.val ∂(μz.prod μ₁)) = _ at hProd
    rw [show (∫⁻ a, cut a ∂μz) = μz S from lintegral_indicator_one hSmeas] at hProd
    rw [← hProd]
    exact lintegral_congr (fun p => (hEq p).symm)
  calc
    (∫⁻ q : Q₁, f q.out.val ∂μ₁) = (μz S)⁻¹ * (μz S * (∫⁻ q : Q₁, f q.out.val ∂μ₁)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hS0 hSfin.ne, one_mul]
    _ ≤ (μz S)⁻¹ * (B * L₀) := mul_le_mul' le_rfl (hFold.trans_le hFull)
    _ = _ := by ac_rfl

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- A fixed algebraic Siegel setup admits a norm-one quotient integral bound from
the minimal modulus times a sufficiently large inverse power of the root logarithms. -/
def AdelicNormOneSiegelIntegrabilityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (j : T₀ ⟶ T),
      IsSiegelAlgebraicSetup F G T i ν T₀ j →
    ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (W : Set (AdelicGroupPoints F G)) (d : ℕ) (L : ℝ≥0∞),
      W.Finite ∧ W ⊆ normOneSubgroup F G ∧ L < ∞ ∧
      ∀ (f : AdelicGroupPoints F G → ℝ≥0∞), Measurable f →
      (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g) →
      ∀ B : ℝ≥0∞,
      (∀ a ∈ weakSimpleRootChamber F T₀ T j G i ν t,
        ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
          f (map F _ G (Standard.unipotentHom i ν ∅) n * map F _ G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i T₀ j a * k * w) ≤
              B * (siegelModulusNN (i := i) (ν := ν) (j := j) a : ℝ≥0∞) *
                ENNReal.ofReal ((siegelRootLogSize i ν j a)⁻¹ ^ d)) →
      ∫⁻ q : NormOneRationalQuotient F G, f q.out.val ∂(normOneRationalQuotientHaarMeasure F G) ≤
        B * L

theorem adelicNormOneSiegelIntegrability : AdelicNormOneSiegelIntegrabilityStatement := by
  intro F _ _ G _ _ _ hG T T₀ i ν j hsetup
  exact exists_normOneSiegelIntegralBound i ν j hG hsetup

end Langlands.Global
