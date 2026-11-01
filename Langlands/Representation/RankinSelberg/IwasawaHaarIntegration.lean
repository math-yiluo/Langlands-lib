import Langlands.Analysis.Local.CompactFactorizationIntegral
import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof
import Langlands.Group.GL.UpperBruhatCells
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Iwasawa integration on the whole group `GL_(n+1)`

Haar measure on `GL_(n+1)(F)` is recovered from Borel coordinates
`(a, u) ↦ diag(a) u` and Haar measure restricted to `K = GL_(n+1)(O)`, by the
published factorization integral. Moving the diagonal factor to the right of the
unipotent factor introduces the inverse upper-Borel modulus.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Langlands.RankinSelberg

namespace IwasawaHaar

open GeneralLinear

section Algebra

variable {E : Type*} [Field E] {n : ℕ}

/-- Borel coordinates `(a, u) ↦ diag(a) u` on the upper triangular subgroup. -/
def borelPoint (x : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E) :
    GeneralLinear (n + 1) E :=
  Iwasawa.diagonalUnits x.1 * (x.2 : GeneralLinear (n + 1) E)

/-- The unipotent factor of a left translate in Borel coordinates. -/
def shiftUnipotent (x₀ : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E)
    (a : Fin (n + 1) → Eˣ) : upperUnipotent (n + 1) E :=
  diagonalConj (x₀.1⁻¹ * a)⁻¹ x₀.2⁻¹

/-- Left translation by `(borelPoint x₀)⁻¹`, written in Borel coordinates. -/
def borelShift (x₀ x : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E) :
    (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E :=
  (x₀.1⁻¹ * x.1, shiftUnipotent x₀ x.1 * x.2)

theorem borelPoint_shift (x₀ x : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E) :
    borelPoint (borelShift x₀ x) = (borelPoint x₀)⁻¹ * borelPoint x := by
  simp only [borelPoint, borelShift, shiftUnipotent, Subgroup.coe_mul, diagonalConj_val,
    Subgroup.coe_inv, map_inv, map_mul]
  group

variable [ValuativeRel E]

/-- Every matrix is `diag(a) u k` with `k` integral. -/
theorem exists_borelPoint_mul [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (y : GeneralLinear (n + 1) E) :
    ∃ x₀ : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E,
      ∃ k₀ ∈ Conductor.integralSubgroup (ValuativeRel.valuation E).integer n,
        y = borelPoint x₀ * k₀ := by
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement E
  obtain ⟨u, hu, lam, k, hk, rfl⟩ := Iwasawa.exists_iwasawa hϖ y
  refine ⟨(fun i => ϖ ^ lam i, diagonalConj (fun i => ϖ ^ lam i)⁻¹ ⟨u, hu⟩), k, hk, ?_⟩
  simp only [borelPoint, diagonalConj_val, map_inv, Iwasawa.torus]
  group

/-- `diag(a) u` is integral exactly when every `a i` is an integral unit and `u`
is integral. -/
theorem borelPoint_mem_iff (x : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E) :
    borelPoint x ∈ Conductor.integralSubgroup (ValuativeRel.valuation E).integer n ↔
      (∀ i, x.1 i ∈ integralUnits (ValuativeRel.valuation E).integer) ∧
        (x.2 : GeneralLinear (n + 1) E) ∈
          Conductor.integralSubgroup (ValuativeRel.valuation E).integer n := by
  constructor
  · intro h
    have hup : (borelPoint x).val.IsUpperTriangular := by
      change ((Iwasawa.diagonalUnits x.1).val * (x.2 : GeneralLinear (n + 1) E).val).IsUpperTriangular
      rw [Iwasawa.diagonalUnits_val]
      exact (Matrix.blockTriangular_diagonal _).mul x.2.2.1
    have hdiag (i : Fin (n + 1)) : (borelPoint x) i i = (x.1 i : E) := by
      change ((Iwasawa.diagonalUnits x.1).val * (x.2 : GeneralLinear (n + 1) E).val) i i = _
      rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
      change (x.1 i : E) * (x.2 : GeneralLinear (n + 1) E) i i = _
      rw [x.2.2.2 i, mul_one]
    have hv (i : Fin (n + 1)) : ValuativeRel.valuation E (x.1 i : E) = 1 := by
      rw [← hdiag i]
      exact Iwasawa.valuation_diag_eq_one _ h hup i
    have hd := Iwasawa.diagonalUnits_mem _ x.1 hv
    refine ⟨fun i => mem_integralUnits_of_valuation_eq_one _ (hv i), ?_⟩
    have hx : (x.2 : GeneralLinear (n + 1) E) = (Iwasawa.diagonalUnits x.1)⁻¹ * borelPoint x := by
      rw [borelPoint, inv_mul_cancel_left]
    rw [hx]
    exact mul_mem (inv_mem hd) h
  · rintro ⟨ha, hu⟩
    exact mul_mem (Iwasawa.diagonalUnits_mem _ x.1
      fun i => valuation_eq_one_of_mem_integralUnits _ (ha i)) hu

end Algebra

section Measure

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [T2Space E] [SecondCountableTopology E]

private instance matrix_locallyCompact (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) E) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → E))

private instance gl_locallyCompact (m : ℕ) : LocallyCompactSpace (GeneralLinear m E) :=
  inferInstance

private instance gl_secondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m E) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) E) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → E))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private instance unipotent_secondCountable (m : ℕ) :
    SecondCountableTopology (upperUnipotent m E) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (upperUnipotent m E : Set (GeneralLinear m E))

private instance unipotent_locallyCompact (m : ℕ) :
    LocallyCompactSpace (upperUnipotent m E) :=
  UpperUnipotent.locallyCompactSpace

private instance units_secondCountable : SecondCountableTopology Eˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

private instance units_locallyCompact : LocallyCompactSpace Eˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := E)).locallyCompactSpace

variable {n : ℕ}

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] [T2Space E] [SecondCountableTopology E] in
theorem continuous_borelPoint [IsTopologicalRing E] :
    Continuous (borelPoint (E := E) (n := n)) :=
  ((continuous_diagonalUnits (n + 1)).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] [T2Space E] [SecondCountableTopology E] in
/-- Diagonal conjugation is jointly continuous in the diagonal and unipotent variables. -/
theorem continuous_diagonalConj_prod [IsTopologicalRing E] :
    Continuous fun p : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E =>
      diagonalConj p.1 p.2 := by
  have h : Continuous fun p : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E =>
      (diagonalConj p.1 p.2 : GeneralLinear (n + 1) E) := by
    simp_rw [diagonalConj_val]
    exact (((continuous_diagonalUnits (n + 1)).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_diagonalUnits (n + 1)).comp continuous_fst).inv
  exact h.subtype_mk _

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] [T2Space E] [SecondCountableTopology E] in
theorem continuous_borelShift_snd [IsTopologicalRing E]
    (x₀ : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E) :
    Continuous (Function.uncurry fun (a : Fin (n + 1) → Eˣ) (u : upperUnipotent (n + 1) E) =>
      shiftUnipotent x₀ a * u) := by
  have hm : Continuous fun a : Fin (n + 1) → Eˣ => ((x₀.1⁻¹ * a)⁻¹ : Fin (n + 1) → Eˣ) :=
    (continuous_const_mul x₀.1⁻¹).inv
  have hd : Continuous fun a : Fin (n + 1) → Eˣ =>
      Iwasawa.diagonalUnits ((x₀.1⁻¹ * a)⁻¹ : Fin (n + 1) → Eˣ) :=
    (continuous_diagonalUnits (n + 1)).comp hm
  have h' : Continuous fun a : Fin (n + 1) → Eˣ =>
      (shiftUnipotent x₀ a : GeneralLinear (n + 1) E) := by
    simp only [shiftUnipotent, diagonalConj_val]
    exact (hd.mul continuous_const).mul hd.inv
  have h : Continuous fun a : Fin (n + 1) → Eˣ => shiftUnipotent x₀ a := h'.subtype_mk _
  have h2 : Continuous fun p : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E =>
      shiftUnipotent x₀ p.1 * p.2 :=
    (h.comp continuous_fst).mul continuous_snd
  exact h2

variable [MeasurableSpace Eˣ] [BorelSpace Eˣ]
  [MeasurableSpace (GeneralLinear (n + 1) E)] [BorelSpace (GeneralLinear (n + 1) E)]
  [MeasurableSpace (upperUnipotent (n + 1) E)] [BorelSpace (upperUnipotent (n + 1) E)]

omit [MeasurableSpace (GeneralLinear (n + 1) E)] [BorelSpace (GeneralLinear (n + 1) E)] in
/-- Left translation in Borel coordinates preserves `da × du`. -/
theorem measurePreserving_borelShift
    (x₀ : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E) :
    MeasurePreserving (borelShift x₀)
      ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
        (unipotentHaar E n))
      ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
        (unipotentHaar E n)) :=
  (measurePreserving_mul_left _ x₀.1⁻¹).skew_product
    (continuous_borelShift_snd x₀).measurable
    (Filter.Eventually.of_forall fun _ => map_mul_left_eq_self _ _)

omit [MeasurableSpace (GeneralLinear (n + 1) E)] [BorelSpace (GeneralLinear (n + 1) E)] in
/-- The Borel coordinates of `K = GL_(n+1)(O)` have mass one. -/
theorem measure_borelPoint_preimage :
    ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
        (unipotentHaar E n))
      (borelPoint ⁻¹' (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
        Set (GeneralLinear (n + 1) E))) = 1 := by
  have hpre : borelPoint ⁻¹' (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
        Set (GeneralLinear (n + 1) E)) =
      (Set.univ.pi fun _ : Fin (n + 1) =>
        (integralUnits (ValuativeRel.valuation E).integer : Set Eˣ)) ×ˢ
        (unipotentIntegralOpen E n : Set (upperUnipotent (n + 1) E)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies,
      SetLike.mem_coe]
    rw [borelPoint_mem_iff]
    apply and_congr Iff.rfl
    change _ ↔ (x.2 : GeneralLinear (n + 1) E) ∈ Conductor.levelSubgroup E n 0
    rw [Conductor.levelSubgroup_zero]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, unipotentHaar_integral]
  simp only [localMultiplicativeHaar_integerUnits, Finset.prod_const_one, mul_one]

omit [MeasurableSpace (GeneralLinear (n + 1) E)] [BorelSpace (GeneralLinear (n + 1) E)] in
/-- The density of diagonal conjugation is measurable in the diagonal variable. -/
theorem measurable_of_map_diagonalConj (w : (Fin (n + 1) → Eˣ) → ℝ≥0∞)
    (hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n) :
    Measurable w := by
  have hU : MeasurableSet (unipotentIntegralOpen E n : Set (upperUnipotent (n + 1) E)) :=
    (unipotentIntegralOpen E n).isOpen.measurableSet
  have hS : MeasurableSet {p : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E |
      diagonalConj p.1 p.2 ∈ (unipotentIntegralOpen E n : Set (upperUnipotent (n + 1) E))} :=
    continuous_diagonalConj_prod.measurable hU
  have heq : w = fun a => unipotentHaar E n (Prod.mk a ⁻¹'
      {p : (Fin (n + 1) → Eˣ) × upperUnipotent (n + 1) E |
        diagonalConj p.1 p.2 ∈ (unipotentIntegralOpen E n : Set (upperUnipotent (n + 1) E))}) := by
    funext a
    have h := congrArg (fun ν : Measure (upperUnipotent (n + 1) E) =>
      ν (unipotentIntegralOpen E n : Set _)) (hw a)
    rw [Measure.map_apply (continuous_diagonalConj a).measurable hU, Measure.smul_apply,
      unipotentHaar_integral, smul_eq_mul, mul_one] at h
    exact h.symm
  rw [heq]
  exact measurable_measure_prodMk_left hS

/-- Moving the diagonal factor to the right of the unipotent factor. -/
theorem lintegral_borelPoint (w : (Fin (n + 1) → Eˣ) → ℝ≥0∞)
    (hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n)
    (h : GeneralLinear (n + 1) E → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x, h (borelPoint x) ∂((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
        (unipotentHaar E n)) =
      ∫⁻ a, w a * ∫⁻ u, h ((u : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a)
        ∂unipotentHaar E n ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E := by
  rw [lintegral_prod (fun x => h (borelPoint x))
    (hh.comp continuous_borelPoint.measurable).aemeasurable]
  apply lintegral_congr
  intro a
  have hc : Measurable (diagonalConj (E := E) (m := n + 1) a) :=
    (continuous_diagonalConj a).measurable
  have hm : Measurable fun v : upperUnipotent (n + 1) E =>
      h ((v : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a) :=
    hh.comp (continuous_subtype_val.mul continuous_const).measurable
  calc ∫⁻ u, h (borelPoint (a, u)) ∂unipotentHaar E n
      = ∫⁻ u, (fun v : upperUnipotent (n + 1) E =>
          h ((v : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a)) (diagonalConj a u)
          ∂unipotentHaar E n := by
        apply lintegral_congr
        intro u
        simp only [borelPoint, diagonalConj_val]
        congr 1
        group
    _ = ∫⁻ v, h ((v : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a)
          ∂((unipotentHaar E n).map (diagonalConj a)) := (lintegral_map hm hc).symm
    _ = w a * ∫⁻ v, h ((v : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a)
          ∂unipotentHaar E n := by
        rw [hw a, lintegral_smul_measure, smul_eq_mul]

/-- **Iwasawa integration on `GL_(n+1)`**, iterated form:
`∫_G f = ∫_K ∫_A w(a) ∫_N f(u a k)`. -/
theorem lintegral_generalLinearHaar (w : (Fin (n + 1) → Eˣ) → ℝ≥0∞)
    (hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n)
    (f : GeneralLinear (n + 1) E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂generalLinearHaar E n =
      ∫⁻ k in (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
          Set (GeneralLinear (n + 1) E)),
        ∫⁻ a, w a * ∫⁻ u, f ((u : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a * k)
          ∂unipotentHaar E n ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar E)
        ∂generalLinearHaar E n := by
  have hKo : IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
      Set (GeneralLinear (n + 1) E)) :=
    Conductor.isOpen_integralSubgroup _ _ (Valuation.isOpen_integer (v := ValuativeRel.valuation E))
  have h1 := CompactFactorization.lintegral_restrict_lintegral_mul (generalLinearHaar E n)
    (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n) hKo.measurableSet
    ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod (unipotentHaar E n))
    borelPoint continuous_borelPoint.measurable (fun y => exists_borelPoint_mul y)
    (fun x₀ => ⟨borelShift x₀, measurePreserving_borelShift x₀,
      fun x => borelPoint_shift x₀ x⟩) f hf
  rw [measure_borelPoint_preimage, one_mul] at h1
  rw [← h1]
  apply lintegral_congr
  intro k
  exact lintegral_borelPoint w hw (fun y => f (y * k)) (hf.comp (measurable_mul_const k))

/-- The Iwasawa coordinates `(u, a, k) ↦ u diag(a) k`. -/
def iwasawaPoint (x : upperUnipotent (n + 1) E × ((Fin (n + 1) → Eˣ) × GeneralLinear (n + 1) E)) :
    GeneralLinear (n + 1) E :=
  (x.1 : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits x.2.1 * x.2.2

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] [T2Space E] [SecondCountableTopology E]
  [MeasurableSpace Eˣ] [BorelSpace Eˣ] [MeasurableSpace (GeneralLinear (n + 1) E)]
  [BorelSpace (GeneralLinear (n + 1) E)] [MeasurableSpace (upperUnipotent (n + 1) E)]
  [BorelSpace (upperUnipotent (n + 1) E)] in
theorem continuous_iwasawaPoint [IsTopologicalRing E] :
    Continuous (iwasawaPoint (E := E) (n := n)) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    ((continuous_diagonalUnits (n + 1)).comp (continuous_fst.comp continuous_snd))).mul
    (continuous_snd.comp continuous_snd)

/-- **Iwasawa integration on `GL_(n+1)`**, product form. -/
theorem lintegral_generalLinearHaar_prod (w : (Fin (n + 1) → Eˣ) → ℝ≥0∞)
    (hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n)
    (f : GeneralLinear (n + 1) E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂generalLinearHaar E n =
      ∫⁻ x, w x.2.1 * f (iwasawaPoint x) ∂((unipotentHaar E n).prod
        ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
          ((generalLinearHaar E n).restrict
            (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
              Set (GeneralLinear (n + 1) E))))) := by
  have hwm := measurable_of_map_diagonalConj w hw
  have hG : Measurable fun x : upperUnipotent (n + 1) E ×
      ((Fin (n + 1) → Eˣ) × GeneralLinear (n + 1) E) => w x.2.1 * f (iwasawaPoint x) :=
    (hwm.comp (measurable_fst.comp measurable_snd)).mul
      (hf.comp continuous_iwasawaPoint.measurable)
  rw [lintegral_prod_symm _ hG.aemeasurable,
    lintegral_prod_symm _ hG.lintegral_prod_left'.aemeasurable,
    lintegral_generalLinearHaar w hw f hf]
  apply lintegral_congr
  intro k
  apply lintegral_congr
  intro a
  dsimp only
  have hc : Continuous fun u : upperUnipotent (n + 1) E =>
      (u : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a * k :=
    (continuous_subtype_val.mul continuous_const).mul continuous_const
  exact (lintegral_const_mul _ (hf.comp hc.measurable)).symm

/-- **Iwasawa integration on `GL_(n+1)`**, measure form. -/
theorem generalLinearHaar_eq_map (w : (Fin (n + 1) → Eˣ) → ℝ≥0∞)
    (hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n) :
    generalLinearHaar E n = Measure.map iwasawaPoint
      (((unipotentHaar E n).prod
        ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
          ((generalLinearHaar E n).restrict
            (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
              Set (GeneralLinear (n + 1) E))))).withDensity fun x => w x.2.1) := by
  have hΨ := continuous_iwasawaPoint (E := E) (n := n) |>.measurable
  ext S hS
  rw [Measure.map_apply hΨ hS, withDensity_apply _ (hΨ hS), ← lintegral_indicator (hΨ hS),
    ← lintegral_indicator_one hS, lintegral_generalLinearHaar_prod w hw _
      (measurable_one.indicator hS)]
  apply lintegral_congr
  intro x
  by_cases hx : iwasawaPoint x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ iwasawaPoint ⁻¹' S from hx),
      Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ iwasawaPoint ⁻¹' S from hx), mul_zero]

/-- **Iwasawa integration on `GL_(n+1)`**, Bochner form for integrable complex
functions, with the unipotent integral innermost. -/
theorem integral_generalLinearHaar (w : (Fin (n + 1) → Eˣ) → ℝ≥0∞)
    (hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n)
    (hwt : ∀ a, w a ≠ ⊤)
    (f : GeneralLinear (n + 1) E → ℂ) (hf : Integrable f (generalLinearHaar E n)) :
    ∫ y, f y ∂generalLinearHaar E n =
      ∫ k in (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
          Set (GeneralLinear (n + 1) E)),
        ∫ a, ((w a).toReal : ℂ) *
          ∫ u, f ((u : GeneralLinear (n + 1) E) * Iwasawa.diagonalUnits a * k)
            ∂unipotentHaar E n
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar E)
        ∂generalLinearHaar E n := by
  have hwm := measurable_of_map_diagonalConj w hw
  have hΨ := (continuous_iwasawaPoint (E := E) (n := n)).measurable
  have hG := generalLinearHaar_eq_map w hw
  have hW : Measurable fun x : upperUnipotent (n + 1) E ×
      ((Fin (n + 1) → Eˣ) × GeneralLinear (n + 1) E) => w x.2.1 :=
    hwm.comp (measurable_fst.comp measurable_snd)
  have hlt : ∀ᵐ x ∂((unipotentHaar E n).prod
      ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
        ((generalLinearHaar E n).restrict
          (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
            Set (GeneralLinear (n + 1) E))))), w x.2.1 < ⊤ :=
    Filter.Eventually.of_forall fun x => (hwt x.2.1).lt_top
  have hfm := hf
  rw [hG] at hfm
  have hint : Integrable (fun x => (w x.2.1).toReal • f (iwasawaPoint x))
      ((unipotentHaar E n).prod
        ((Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar E).prod
          ((generalLinearHaar E n).restrict
            (Conductor.integralSubgroup (ValuativeRel.valuation E).integer n :
              Set (GeneralLinear (n + 1) E))))) :=
    (integrable_withDensity_iff_integrable_smul' hW hlt).1
      ((integrable_map_measure hfm.aestronglyMeasurable hΨ.aemeasurable).1 hfm)
  conv_lhs => rw [hG]
  rw [integral_map hΨ.aemeasurable hfm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hW hlt, integral_prod_symm _ hint,
    integral_prod_symm _ hint.integral_prod_right]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [iwasawaPoint]
  rw [integral_smul, Complex.real_smul]

end Measure

section Padic

universe uF

/-- **Iwasawa integration on `GL_(n+1)(F)`** for a supplied `p`-adic field, with
the normalizations of `QuotientIwasawaIntegrationStatement`: Haar measure is the
pushforward of `du × (da × dk)` under `(u, a, k) ↦ u diag(a) k`, weighted by the
inverse upper-Borel modulus `δ(a)⁻¹ = ∏_{i<j} |a_i / a_j|⁻¹`. -/
theorem generalLinearHaar_eq_map_iwasawa {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    let A := Fin (n + 1) → F.Carrierˣ
    let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
      localMultiplicativeHaar F.Carrier)
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
    let dk := (generalLinearHaar F.Carrier n).restrict (K : Set _)
    let δ : A → ℝ := fun a =>
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier)
    generalLinearHaar F.Carrier n =
      Measure.map
        (fun x : upperUnipotent (n + 1) F.Carrier ×
            (A × Langlands.GeneralLinear (n + 1) F.Carrier) =>
          x.1.val * Iwasawa.diagonalUnits x.2.1 * x.2.2)
        (((unipotentHaar F.Carrier n).prod (da.prod dk)).withDensity
          (fun x => ENNReal.ofReal ((δ x.2.1)⁻¹))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  intro A da K dk δ
  refine generalLinearHaar_eq_map (fun a => ENNReal.ofReal ((δ a)⁻¹)) fun a => ?_
  rw [diagonalConj_map F T n a, ENNReal.smul_def]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, singleton_modulus_real F T a]

/-- **Iwasawa integration on `GL_(n+1)(F)`**, Bochner form, with the
normalizations of `generalLinearHaar_eq_map_iwasawa`:
`∫_G f = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk` for integrable `f`. -/
theorem integral_generalLinearHaar_iwasawa {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    let A := Fin (n + 1) → F.Carrierˣ
    let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
      localMultiplicativeHaar F.Carrier)
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
    let δ : A → ℝ := fun a =>
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier)
    ∀ f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ,
      Integrable f (generalLinearHaar F.Carrier n) →
        ∫ y, f y ∂generalLinearHaar F.Carrier n =
          ∫ k in (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)),
            ∫ a, (((δ a)⁻¹ : ℝ) : ℂ) *
              ∫ u, f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F.Carrier n ∂da
            ∂generalLinearHaar F.Carrier n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  intro A da K δ f hf
  have hw : ∀ a, (unipotentHaar F.Carrier n).map (diagonalConj a) =
      ENNReal.ofReal ((δ a)⁻¹) • unipotentHaar F.Carrier n := by
    intro a
    rw [diagonalConj_map F T n a, ENNReal.smul_def]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, singleton_modulus_real F T a]
  have hδ (a : A) : (ENNReal.ofReal ((δ a)⁻¹)).toReal = (δ a)⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.2 (Finset.prod_nonneg fun i _ =>
      Finset.prod_nonneg fun j _ => T.normalizedAbs_nonneg _))
  rw [integral_generalLinearHaar _ hw (fun _ => ENNReal.ofReal_ne_top) f hf]
  simp only [hδ]
  rfl

end Padic

end IwasawaHaar

end Langlands.RankinSelberg
