import Langlands.Representation.RankinSelberg.IwasawaTorusSumProof
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof
import Langlands.AllField.Representation.RankinSelberg.IwasawaTorusSumStatement
/-!
# Discrete torus decomposition of the normalized Iwasawa pushforward

The published uniformizer-coset partition reduces the weighted torus integral to
a countable sum. The modulus is constant on each coset, and left invariance of
restricted compact Haar absorbs its integral diagonal unit factor.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding IwasawaTorusPartitionStatement IwasawaTorusSumStatement iwasawaTorusPartition iwasawaTorusSum
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

private theorem normalizedAbs_integralUnit 
    (F : Type uF) [Field F] (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ a : Fˣ,
      a ∈ integralUnits (ValuativeRel.valuation F).integer →
      T.normalizedAbs (a : F) = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro a ha
  rw [T.normalizedAbs_eq_one_iff_discreteValuation]
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
    (ValuativeRel.valuation F (a : F)) = 1
  rw [valuation_eq_one_of_mem_integralUnits _ ha, map_one]

private theorem modulus_integralUnit_shift 
    (F : Type uF) [Field F] (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (t u : Fin m → Fˣ),
      (∀ i, u i ∈ integralUnits (ValuativeRel.valuation F).integer) →
      (∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        T.normalizedAbs (((t * u) i / (t * u) j : Fˣ) : F)) =
      (∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        T.normalizedAbs ((t i / t j : Fˣ) : F)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro t u hu
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  have hdiv : (t * u) i / (t * u) j = (t i / t j) * (u i / u j) := by
    change t i * u i / (t j * u j) = _
    exact mul_div_mul_comm _ _ _ _
  rw [hdiv, Units.val_mul, T.normalizedAbs_mul,
    normalizedAbs_integralUnit F T _ ((integralUnits _).div_mem (hu i) (hu j)), mul_one]

private theorem restrictedHaar_mul_left {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [Measure.IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G)) {g : G} (hg : g ∈ K) :
    Measure.map (g * ·) (μ.restrict (K : Set G)) = μ.restrict (K : Set G) := by
  have hpre : (fun x : G => g * x) ⁻¹' (K : Set G) = (K : Set G) := by
    ext x
    exact K.mul_mem_cancel_left hg
  have h := Measure.restrict_map (μ := μ) (measurable_const_mul g) hK
  rw [map_mul_left_eq_self, hpre] at h
  exact h.symm

private theorem restrictedHaar_absorb {G Q : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [MeasurableSpace Q]
    (μ : Measure G) [Measure.IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (p : G → Q) (hp : Measurable p) (g k : G) (hk : k ∈ K) :
    Measure.map (fun x => p (g * (k * x))) (μ.restrict (K : Set G)) =
      Measure.map (fun x => p (g * x)) (μ.restrict (K : Set G)) := by
  calc
    _ = Measure.map (fun x => p (g * x))
        (Measure.map (k * ·) (μ.restrict (K : Set G))) :=
      (Measure.map_map (hp.comp (measurable_const_mul g)) (measurable_const_mul k)).symm
    _ = _ := by rw [restrictedHaar_mul_left μ K hK hk]

private theorem weighted_partition_pushforward
    {A G Q L : Type*} [MeasurableSpace A] [MeasurableSpace G] [MeasurableSpace Q]
    [Countable L] (da : Measure A) (dk : Measure G) [SFinite dk]
    (U : Set A) (hU : MeasurableSet U) (hUone : da U = 1)
    (C : L → Set A) (hC : ∀ l, MeasurableSet (C l))
    (hdis : Pairwise (fun l l' => Disjoint (C l) (C l')))
    (hcover : (⋃ l, C l) = Set.univ)
    (shift : L → A → A) (hshift : ∀ l, Measurable (shift l))
    (hmap : ∀ l, Measure.map (shift l) (da.restrict U) = da.restrict (C l))
    (q : A × G → Q) (hq : Measurable q)
    (qL : L → G → Q) (w : A → ℝ≥0∞) (hw : Measurable w) (wL : L → ℝ≥0∞)
    (hwshift : ∀ l u, u ∈ U → w (shift l u) = wL l)
    (habsorb : ∀ l u, u ∈ U →
      Measure.map (fun k => q (shift l u, k)) dk = Measure.map (qL l) dk) :
    Measure.map q ((da.prod dk).withDensity (fun x => w x.1)) =
      Measure.sum (fun l => wL l • Measure.map (qL l) dk) := by
  classical
  apply Measure.ext
  intro s hs
  let f : A × G → ℝ≥0∞ := fun x => s.indicator (fun _ => 1) (q x)
  have hf : Measurable f := (measurable_const.indicator hs).comp hq
  let I : A → ℝ≥0∞ := fun a => w a * ∫⁻ k, f (a, k) ∂dk
  have hI : Measurable I := hw.mul hf.lintegral_prod_right'
  have hpart : da = Measure.sum (fun l => da.restrict (C l)) := by
    calc
      da = da.restrict Set.univ := (Measure.restrict_univ).symm
      _ = da.restrict (⋃ l, C l) := by rw [hcover]
      _ = _ := Measure.restrict_iUnion hdis hC
  have hfiber (a : A) :
      (∫⁻ k, f (a, k) ∂dk) = Measure.map (fun k => q (a, k)) dk s := by
    have hqa : Measurable (fun k => q (a, k)) :=
      hq.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hqa hs, ← lintegral_indicator_one (hqa hs)]
    rfl
  have hterm (l : L) :
      (∫⁻ a in C l, I a ∂da) = wL l * Measure.map (qL l) dk s := by
    rw [← hmap l, lintegral_map hI (hshift l)]
    calc
      (∫⁻ u in U, I (shift l u) ∂da) =
          ∫⁻ _u in U, wL l * Measure.map (qL l) dk s ∂da := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hU] with u hu
        dsimp only [I]
        rw [hwshift l u hu, hfiber, habsorb l u hu]
      _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, hUone, mul_one]
  calc
    Measure.map q ((da.prod dk).withDensity (fun x => w x.1)) s =
        ∫⁻ x, w x.1 * f x ∂da.prod dk := by
      rw [Measure.map_apply hq hs, withDensity_apply _ (hq hs),
        ← lintegral_indicator (hq hs)]
      apply lintegral_congr
      intro x
      by_cases hx : q x ∈ s <;> simp [f, hx]
    _ = ∫⁻ a, I a ∂da := by
      rw [lintegral_prod (fun x : A × G => w x.1 * f x)
        ((hw.comp measurable_fst).mul hf).aemeasurable]
      apply lintegral_congr
      intro a
      exact lintegral_const_mul (w a) (hf.comp (measurable_const.prodMk measurable_id))
    _ = ∑' l, ∫⁻ a in C l, I a ∂da := by
      calc
        (∫⁻ a, I a ∂da) = ∫⁻ a, I a ∂Measure.sum (fun l => da.restrict (C l)) :=
          congrArg (fun μ => ∫⁻ a, I a ∂μ) hpart
        _ = _ := lintegral_sum_measure _ _
    _ = ∑' l, wL l * Measure.map (qL l) dk s := by simp_rw [hterm]
    _ = (Measure.sum (fun l => wL l • Measure.map (qL l) dk)) s := by
      rw [Measure.sum_apply _ hs]
      rfl

private theorem iwasawaTorusSum_from_partition 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ ϖ : Fˣ,
    let A := Fin (n + 1) → Fˣ
    let G := Langlands.GeneralLinear (n + 1) F
    let da : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
    let dk : Measure G := (generalLinearHaar F n).restrict (K : Set G)
    let U : Set A := {u | ∀ i, u i ∈ integralUnits (ValuativeRel.valuation F).integer}
    let t : (Fin (n + 1) → ℤ) → A := fun lam i => ϖ ^ lam i
    let C := fun lam => (fun u : A => t lam * u) '' U
    let δ : A → ℝ := fun a =>
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        T.normalizedAbs ((a i / a j : Fˣ) : F)
    let q : A × G → LeftUnipotentQuotient n F := fun x =>
      leftQuotientMap (upperUnipotent (n + 1) F)
        (Iwasawa.diagonalUnits x.1 * x.2)
    let qLam := fun (lam : Fin (n + 1) → ℤ) (k : G) =>
      leftQuotientMap (upperUnipotent (n + 1) F) (Iwasawa.torus ϖ lam * k)
    (MeasurableSet U ∧ da U = 1 ∧
      (∀ lam, MeasurableSet (C lam) ∧ da (C lam) = 1 ∧
        Measure.map (fun u => t lam * u) (da.restrict U) = da.restrict (C lam)) ∧
      Pairwise (fun lam lam' => Disjoint (C lam) (C lam')) ∧
      (⋃ lam, C lam) = Set.univ) →
    Measure.map q ((da.prod dk).withDensity (fun x => ENNReal.ofReal ((δ x.1)⁻¹))) =
      Measure.sum (fun lam => ENNReal.ofReal ((δ (t lam))⁻¹) • Measure.map (qLam lam) dk) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : SecondCountableTopology Fˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  have : T2Space F := inferInstance
  intro ϖ
  let A := Fin (n + 1) → Fˣ
  let G := Langlands.GeneralLinear (n + 1) F
  let da : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let dk : Measure G := (generalLinearHaar F n).restrict (K : Set G)
  let U : Set A := {u | ∀ i, u i ∈ integralUnits (ValuativeRel.valuation F).integer}
  let t : (Fin (n + 1) → ℤ) → A := fun lam i => ϖ ^ lam i
  let C := fun lam => (fun u : A => t lam * u) '' U
  let δ : A → ℝ := fun a =>
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((a i / a j : Fˣ) : F)
  let q : A × G → LeftUnipotentQuotient n F := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F)
      (Iwasawa.diagonalUnits x.1 * x.2)
  let qLam := fun (lam : Fin (n + 1) → ℤ) (k : G) =>
    leftQuotientMap (upperUnipotent (n + 1) F) (Iwasawa.torus ϖ lam * k)
  change (MeasurableSet U ∧ da U = 1 ∧
    (∀ lam, MeasurableSet (C lam) ∧ da (C lam) = 1 ∧
      Measure.map (fun u => t lam * u) (da.restrict U) = da.restrict (C lam)) ∧
    Pairwise (fun lam lam' => Disjoint (C lam) (C lam')) ∧
    (⋃ lam, C lam) = Set.univ) → _
  rintro ⟨hU, hUone, hC, hdis, hcover⟩
  have hdk : dk Set.univ = 1 := by
    change (generalLinearHaar F n).restrict (K : Set G) Set.univ = 1
    rw [Measure.restrict_apply_univ]
    exact generalLinearHaar_integralSubgroup F n
  let : IsFiniteMeasure dk := ⟨by rw [hdk]; exact ENNReal.one_lt_top⟩
  have hK : MeasurableSet (K : Set G) := by
    change MeasurableSet
      (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n : Set G)
    rw [← Conductor.levelSubgroup_zero F n]
    exact (Conductor.levelOpenSubgroup F n 0).isOpen.measurableSet
  have hq : Measurable q :=
    ((leftQuotient_isOpenQuotientMap _).continuous.comp
      (((GeneralLinear.continuous_diagonalUnits (n + 1)).comp continuous_fst).mul continuous_snd)).measurable
  have hAbs : Continuous T.normalizedAbs :=
    NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
  have hδ : Continuous δ := by
    apply continuous_finsetProd
    intro i _
    apply continuous_finsetProd
    intro j _
    have hc : Continuous (fun a : A => ((a i / a j : Fˣ) : F)) := by
      simp only [div_eq_mul_inv]
      exact Units.continuous_val.comp
        ((continuous_apply i).mul (continuous_inv.comp (continuous_apply j)))
    exact hAbs.comp hc
  have hδpos (a : A) : 0 < δ a := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    exact T.normalizedAbs_pos (Units.ne_zero (a i / a j))
  have hw : Measurable (fun a : A => ENNReal.ofReal ((δ a)⁻¹)) :=
    (hδ.inv₀ (fun a => (hδpos a).ne')).measurable.ennreal_ofReal
  apply weighted_partition_pushforward da dk U hU hUone C (fun lam => (hC lam).1)
    hdis hcover (fun lam u => t lam * u) (fun _ => measurable_const_mul _)
    (fun lam => (hC lam).2.2) q hq qLam _ hw
    (fun lam => ENNReal.ofReal ((δ (t lam))⁻¹))
  · intro lam u hu
    rw [show δ (t lam * u) = δ (t lam) from
      modulus_integralUnit_shift F T (n + 1) (t lam) u hu]
  · intro lam u hu
    have hdu : Iwasawa.diagonalUnits u ∈ K :=
      Iwasawa.diagonalUnits_mem _ u
        (fun i => valuation_eq_one_of_mem_integralUnits _ (hu i))
    have hfun : (fun k => q (t lam * u, k)) =
        fun k => leftQuotientMap (upperUnipotent (n + 1) F)
          (Iwasawa.torus ϖ lam * (Iwasawa.diagonalUnits u * k)) := by
      funext k
      simp only [q, map_mul, mul_assoc]
      rfl
    rw [hfun]
    exact restrictedHaar_absorb (generalLinearHaar F n) K hK
      (leftQuotientMap (upperUnipotent (n + 1) F))
      (leftQuotient_isOpenQuotientMap _).continuous.measurable
      (Iwasawa.torus ϖ lam) (Iwasawa.diagonalUnits u) hdu

/-- The normalized torus/compact pushforward is the inverse-modulus-weighted sum
of compact pushforwards at every uniformizer exponent vector. -/
theorem iwasawaTorusSum : IwasawaTorusSumStatement.{uF} := by
  intro F _ T n
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ϖ hϖ
  exact iwasawaTorusSum_from_partition F T n ϖ
    (iwasawaTorusPartition F T (n + 1) ϖ hϖ)

end Langlands.AllField.RankinSelberg
