import Langlands.Representation.RankinSelberg.UnitaryCellBound
import Langlands.Representation.Whittaker.MirabolicQuotientMeasure
import Langlands.Representation.RankinSelberg.QuotientTorusEnvelope
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Unramified.StandardHeckeSum

/-!
# Single-row cells of the mirabolic quotient and their masses
-/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedUnitary

open MeasureTheory GeneralLinear HarmonicAnalysis Induction QuotientIntegration Whittaker

universe uF uV

/-! ### Single-row torus elements -/

section Torus

variable {K : Type uF} [Field K]

/-- The exponent `(m, 0, …, 0)`. -/
def singleRow (k m : ℕ) : Fin (k + 1) → ℤ := fun i => if i = 0 then (m : ℤ) else 0

theorem levi_torus (ϖ : Kˣ) {k : ℕ} (lam : Fin (k + 1) → ℤ) :
    (Mirabolic.levi (Iwasawa.torus ϖ lam)).val = Iwasawa.torus ϖ (Fin.snoc lam 0) := by
  apply Units.ext
  ext i j
  rw [Iwasawa.torus_val]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h := Mirabolic.levi_bottom (Iwasawa.torus ϖ lam) j
    change (Mirabolic.levi (Iwasawa.torus ϖ lam)).val.val (Fin.last _) j = _
    rw [h]
    by_cases hj : j = Fin.last _
    · subst hj
      simp
    · rw [ite_eq_right hj, Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Mirabolic.levi_last, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne]
    · rw [Mirabolic.levi_first, Iwasawa.torus_val]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [Matrix.diagonal_apply_ne _ hij,
          Matrix.diagonal_apply_ne _ (fun h => hij (Fin.castSucc_injective _ h))]

theorem snoc_singleRow (k m : ℕ) :
    (Fin.snoc (singleRow k m) 0 : Fin (k + 2) → ℤ) =
      fun i => if i = 0 then (m : ℤ) else 0 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last, ite_eq_right (Fin.last_pos.ne')]
  · rw [Fin.snoc_castSucc, singleRow]
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [ite_eq_right hi, ite_eq_right]
      intro h
      exact hi (Fin.castSucc_injective _ (h.trans Fin.castSucc_zero.symm))

/-- The mirabolic element `diag(ϖ^m, 1, …, 1)`. -/
def rowElement (ϖ : Kˣ) (k m : ℕ) : mirabolic (k + 1) K :=
  Mirabolic.levi (Iwasawa.torus ϖ (singleRow k m))

theorem rowElement_val (ϖ : Kˣ) (k m : ℕ) :
    (rowElement ϖ k m).val = Iwasawa.torus ϖ (fun i : Fin (k + 2) => if i = 0 then (m : ℤ) else 0) := by
  rw [rowElement, levi_torus, snoc_singleRow]

end Torus

/-! ### The torus lower bound for the unipotent quotient measure -/

section Masses

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A set of `N \ GL_(k+1)` containing the classes of `ϖ^λ k` for all integral `k` has
mass at least the inverse modulus of `ϖ^λ`. -/
theorem density_le_quotientMeasure (T : F.TopologicalData) (k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (k + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (k + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient k F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient k F.Carrier) := ⟨rfl⟩
    ∀ ϖ : F.Carrierˣ, Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
    ∀ (lam : Fin (k + 1) → ℤ) (Y : Set (LeftUnipotentQuotient k F.Carrier)),
      (∀ x ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k,
        leftQuotientMap (upperUnipotent (k + 1) F.Carrier) (Iwasawa.torus ϖ lam * x) ∈ Y) →
      ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) ≤
        unipotentQuotientHaar F.Carrier k Y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (k + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (k + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient k F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient k F.Carrier) := ⟨rfl⟩
  intro ϖ hϖ lam Y hY
  let G := Langlands.GeneralLinear (k + 1) F.Carrier
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k
  let q := fun (x : G) => leftQuotientMap (upperUnipotent (k + 1) F.Carrier)
    (Iwasawa.torus ϖ lam * x)
  have hq : Measurable q :=
    ((leftQuotient_isOpenQuotientMap _).continuous.comp
      (continuous_const.mul continuous_id)).measurable
  rw [QuotientTorusEnvelope.quotientMeasure_eq_sum_torus F T k _
    (unipotentQuotientHaar_isCompatible F.Carrier k) ϖ hϖ]
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ lam) Y)
  rw [Measure.smul_apply, smul_eq_mul]
  have h1 : (1 : ENNReal) ≤ Measure.map q ((generalLinearHaar F.Carrier k).restrict (K : Set G)) Y := by
    refine le_trans ?_ (Measure.le_map_apply hq.aemeasurable Y)
    calc (1 : ENNReal) = (generalLinearHaar F.Carrier k) (K : Set G) :=
          (generalLinearHaar_integralSubgroup F.Carrier k).symm
      _ = ((generalLinearHaar F.Carrier k).restrict (K : Set G)) (K : Set G) :=
          (Measure.restrict_apply_self _ _).symm
      _ ≤ _ := measure_mono (fun x hx => hY x hx)
  calc ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam)
      = ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

/-- The inverse modulus of `diag(ϖ^m, 1, …, 1)` in `GL_(k+1)` is `q^(k m)`. -/
theorem density_singleRow (T : F.TopologicalData) (k m : ℕ) :
    QuotientTorusEnvelope.density F T (LocalFactor.PadicAbelian.uniformizerUnit T)
      (singleRow k m) = (T.residueCardinality : ℝ) ^ (k * m) := by
  set ϖ := LocalFactor.PadicAbelian.uniformizerUnit T
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)
  have hpair : ∀ a b : ℤ, T.normalizedAbs (((ϖ ^ a) / (ϖ ^ b) : F.Carrierˣ) : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-(a - b)) := by
    intro a b
    rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add, ← sub_eq_add_neg]
    exact LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T (a - b)
  have hcard : (Finset.univ.filter (fun j : Fin (k + 1) => (0 : Fin (k + 1)) < j)).card = k := by
    have he : Finset.univ.filter (fun j : Fin (k + 1) => (0 : Fin (k + 1)) < j) =
        Finset.univ.erase 0 := by
      ext j
      simp [Fin.pos_iff_ne_zero]
    rw [he, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rfl
  rw [QuotientTorusEnvelope.density, Fin.prod_univ_succ]
  have h0 : ∏ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => (0 : Fin (k + 1)) < j),
      T.normalizedAbs (((ϖ ^ singleRow k m 0) / (ϖ ^ singleRow k m j) : F.Carrierˣ) :
        F.Carrier) = ((T.residueCardinality : ℝ) ^ (-(m : ℤ))) ^ k := by
    rw [Finset.prod_congr rfl (g := fun _ => (T.residueCardinality : ℝ) ^ (-(m : ℤ))),
      Finset.prod_const, hcard]
    intro j hj
    have hj0 : j ≠ 0 := (Fin.pos_iff_ne_zero.mp (Finset.mem_filter.mp hj).2)
    rw [hpair, singleRow, singleRow, ite_eq_left rfl, ite_eq_right hj0, sub_zero]
  have h1 : ∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => i.succ < j),
      T.normalizedAbs (((ϖ ^ singleRow k m i.succ) / (ϖ ^ singleRow k m j) : F.Carrierˣ) :
        F.Carrier) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j hj
    have hj0 : j ≠ 0 := by
      intro h
      have := (Finset.mem_filter.mp hj).2
      rw [h] at this
      exact absurd this (Fin.not_lt_zero _)
    rw [hpair, singleRow, singleRow, ite_eq_right (Fin.succ_ne_zero i), ite_eq_right hj0,
      sub_zero, neg_zero, zpow_zero]
  rw [h0, h1, mul_one, ← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_natCast]
  congr 1
  push_cast
  ring

end Masses

/-! ### The measure on `N \ P` and the masses of single-row cells -/

section MirabolicMeasure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance cellFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance cellFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance cellFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The integral points `GL_(k+2)(O) ∩ P` of the mirabolic group. -/
def mirabolicIntegral (k : ℕ) : OpenSubgroup (mirabolic (k + 1) F.Carrier) :=
  (Conductor.levelOpenSubgroup F.Carrier (k + 1) 0).comap (mirabolic (k + 1) F.Carrier).subtype
    continuous_subtype_val

theorem mem_mirabolicIntegral {k : ℕ} (g : mirabolic (k + 1) F.Carrier) :
    g ∈ mirabolicIntegral F k ↔
      g.val ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer (k + 1) := by
  change g.val ∈ Conductor.levelSubgroup F.Carrier (k + 1) 0 ↔ _
  rw [Conductor.levelSubgroup_zero]

theorem isCompact_mirabolicIntegral (k : ℕ) :
    IsCompact (mirabolicIntegral F k : Set (mirabolic (k + 1) F.Carrier)) := by
  have := F.canonicalTopologicalData.fieldT2
  exact Mirabolic.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (Conductor.isCompact_levelOpenSubgroup F.Carrier (k + 1) 0)

theorem levi_mem_mirabolicIntegral {k : ℕ} (a : Langlands.GeneralLinear (k + 1) F.Carrier)
    (ha : a ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k) :
    Mirabolic.levi a ∈ mirabolicIntegral F k :=
  (mem_mirabolicIntegral F _).2 (Iwasawa.rankInclusion_mem (ValuativeRel.valuation F.Carrier) ha)

/-- A right-invariant measure on `N \ P_(k+1)` with positive finite orbit masses, under
which the single-row cell of `diag(ϖ^m, 1, …, 1)` has mass at least `q^(k m)`. -/
theorem exists_mirabolicMeasure (k : ℕ)
    [MeasurableSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent (k + 1) F.Carrier))]
    [BorelSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent (k + 1) F.Carrier))] :
    ∃ ν : Measure (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent (k + 1) F.Carrier)),
      IsFiniteMeasureOnCompacts ν ∧
      (∀ g : mirabolic (k + 1) F.Carrier,
        MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν) ∧
      (∀ J : OpenSubgroup (mirabolic (k + 1) F.Carrier),
        IsCompact (J : Set (mirabolic (k + 1) F.Carrier)) →
        0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤) ∧
      ∀ m : ℕ, ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (k * m)) ≤
        ν (compactOpenQuotientOrbit _
          (conjSub (rowElement F.canonicalTopologicalData.uniformizerUnit k m)
            (mirabolicIntegral F k))) := by
  let T := F.canonicalTopologicalData
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear.upperUnipotent (k + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear.upperUnipotent (k + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := borel _
  have : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (GeneralLinear.upperUnipotent (k + 1) F.Carrier)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    (GeneralLinear.upperUnipotent (k + 1) F.Carrier)) := ⟨rfl⟩
  have hμ := RankinSelberg.unipotentQuotientHaar_isCompatible F.Carrier k
  let μ := RankinSelberg.unipotentQuotientHaar F.Carrier k
  let e := (MirabolicQuotient.quotientHomeomorph (n := k + 1) (F := F.Carrier)).symm
  have hinv : ∀ g : mirabolic (k + 1) F.Carrier,
      MeasurePreserving (QuotientIntegration.rightTranslate _ g) (μ.map e) (μ.map e) := by
    intro g
    refine ⟨(QuotientIntegration.rightTranslate _ g).continuous.measurable, ?_⟩
    have hcomm : (QuotientIntegration.rightTranslate (Mirabolic.upperUnipotent (k + 1) F.Carrier) g) ∘ e =
        e ∘ QuotientIntegration.rightTranslate (GeneralLinear.upperUnipotent (k + 1) F.Carrier)
          (Mirabolic.projection g) :=
      funext fun q => MirabolicQuotient.rightTranslate_quotientHomeomorph_symm g q
    rw [Measure.map_map (QuotientIntegration.rightTranslate _ g).continuous.measurable
      e.continuous.measurable, hcomm,
      ← Measure.map_map e.continuous.measurable
        (QuotientIntegration.rightTranslate _ _).continuous.measurable,
      (hμ.right_invariant (Mirabolic.projection g)).map_eq]
  refine ⟨μ.map e, Measure.IsFiniteMeasureOnCompacts.map μ e, hinv, fun J hJ => ?_, fun m => ?_⟩
  · have hm := (QuotientIntegration.isOpen_compactOpenQuotientOrbit
      (Mirabolic.upperUnipotent (k + 1) F.Carrier) J).measurableSet
    rw [Measure.map_apply e.continuous.measurable hm]
    have hpre : e ⁻¹' compactOpenQuotientOrbit _ J = e.symm '' compactOpenQuotientOrbit _ J :=
      (congrFun e.image_symm _).symm
    rw [hpre]
    exact hμ.measure_pos_lt_top
      ((QuotientIntegration.isCompact_compactOpenQuotientOrbit _ J hJ).image e.symm.continuous)
      (e.symm.isOpenMap _ (QuotientIntegration.isOpen_compactOpenQuotientOrbit _ J))
      ((QuotientIntegration.compactOpenQuotientOrbit_nonempty _ J).image _)
  · let ϖ := F.canonicalTopologicalData.uniformizerUnit
    let t := rowElement ϖ k m
    let O := compactOpenQuotientOrbit (Mirabolic.upperUnipotent (k + 1) F.Carrier)
      (conjSub t (mirabolicIntegral F k))
    let R := QuotientIntegration.rightTranslate (Mirabolic.upperUnipotent (k + 1) F.Carrier) t⁻¹
    have hR := hinv t⁻¹
    calc ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (k * m))
        ≤ μ (e ⁻¹' (R ⁻¹' O)) := by
          rw [← density_singleRow F T k m]
          apply density_le_quotientMeasure F T k ϖ
            (Unramified.uniformizerUnit_isUniformizingElement F) (singleRow k m)
          intro x hx
          refine ⟨t * Mirabolic.levi x * t⁻¹,
            conj_mem_conjSub t _ (levi_mem_mirabolicIntegral F x hx), ?_⟩
          change Quotient.mk _ (t * Mirabolic.levi x * t⁻¹) =
            Quotient.mk _ (Mirabolic.levi (Iwasawa.torus ϖ (singleRow k m) * x) * t⁻¹)
          rw [map_mul]
          rfl
      _ ≤ (μ.map e) (R ⁻¹' O) := Measure.le_map_apply e.continuous.measurable.aemeasurable _
      _ ≤ ((μ.map e).map R) O := Measure.le_map_apply hR.measurable.aemeasurable O
      _ = (μ.map e) O := by rw [hR.map_eq]

/-- Distinct single-row elements lie in distinct cells `N t K`. -/
theorem rowElement_ne (k : ℕ) {i j : ℕ} (hij : i ≠ j) (h : Mirabolic.upperUnipotent (k + 1) F.Carrier)
    (κ : mirabolic (k + 1) F.Carrier) (hκ : κ ∈ mirabolicIntegral F k) :
    rowElement F.canonicalTopologicalData.uniformizerUnit k i ≠
      (h : mirabolic (k + 1) F.Carrier) *
        rowElement F.canonicalTopologicalData.uniformizerUnit k j * κ := by
  intro he
  have he' := congrArg Subtype.val he
  simp only [Subgroup.coe_mul, rowElement_val] at he'
  have hexp := Iwasawa.iwasawa_exponent_unique
    (Unramified.uniformizerUnit_isUniformizingElement F)
    (u := 1) (k := 1) (one_mem _) h.property (one_mem _) ((mem_mirabolicIntegral F κ).1 hκ)
    (by rw [one_mul, mul_one]; exact he')
  have h0 := congrFun hexp 0
  simp only [ite_true] at h0
  exact hij (by exact_mod_cast h0)

/-- **Square-summability on single-row cells.** For an irreducible admissible unitarizable
representation `ρ` of `GL_(k+2)(F)` with a nonzero standard Whittaker functional `ℓ` and a
`GL_(k+2)(O)`-fixed vector `v`, the partial sums of
`q^(k m) |ℓ(ρ(diag(ϖ^m, 1, …, 1)) v)|²` are bounded. -/
theorem rowSum_bounded (k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (hadm : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) (hunit : IsUnitarizable ρ)
    (ℓ : glFunctionals ψ (k + 1) ρ) (hℓ : ℓ.val ≠ 0)
    (v : V) (hv : v ∈ fixedVectors ρ (Correspondence.sphericalSubgroup F (k + 1))) :
    ∃ C : ℝ, ∀ M : ℕ, ∑ m ∈ Finset.range M,
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (k * m) *
        ‖ℓ.val (ρ (Iwasawa.torus F.canonicalTopologicalData.uniformizerUnit
          (fun i : Fin (k + 1 + 1) => if i = 0 then (m : ℤ) else 0)) v)‖ ^ 2 ≤ C := by
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent (k + 1) F.Carrier)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent (k + 1) F.Carrier)) := ⟨rfl⟩
  obtain ⟨ν, hfin, hinv, hmass, hrow⟩ := exists_mirabolicMeasure F k
  have hvK : ∀ g ∈ mirabolicIntegral F k, ρ g.val v = v := by
    intro g hg
    have h := hv
    rw [fixedVectors, Representation.mem_invariants] at h
    exact h ⟨g.val, (mem_mirabolicIntegral F g).1 hg⟩
  obtain ⟨C, hC⟩ := padicCellBound F (k + 1) ψ ρ hadm hirr hunit ℓ hℓ ν hfin hinv hmass v
    (mirabolicIntegral F k) (isCompact_mirabolicIntegral F k) hvK
  refine ⟨C, fun M => ?_⟩
  have hb := hC (Finset.range M) (fun m => rowElement F.canonicalTopologicalData.uniformizerUnit k m)
    (fun i _ j _ hij h κ hκ => rowElement_ne F k hij h κ hκ)
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) hb
  rw [rowElement_val]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hfin' := (hmass _ (isCompact_conjSub
    (rowElement F.canonicalTopologicalData.uniformizerUnit k m) _
    (isCompact_mirabolicIntegral F k))).2
  exact (ENNReal.ofReal_le_iff_le_toReal hfin'.ne).1 (hrow m)

end MirabolicMeasure

end Langlands.RankinSelberg.UnramifiedUnitary
