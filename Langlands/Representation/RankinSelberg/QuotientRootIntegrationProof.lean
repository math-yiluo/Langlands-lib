import Langlands.Representation.RankinSelberg.QuotientRootIntegrationStatement
import Langlands.Representation.RankinSelberg.RootCoordinateProof
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF

private theorem map_density_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {e : X → Y} (he : MeasurePreserving e μ ν)
    {r : Y → ENNReal} (hr : Measurable r) :
    Measure.map e (μ.withDensity (r ∘ e)) = ν.withDensity r := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply he.measurable hs,
    withDensity_apply _ (he.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (he.measurable hs), ← lintegral_indicator hs]
  calc
    _ = ∫⁻ a, s.indicator r (e a) ∂μ := by
      apply lintegral_congr
      intro a
      by_cases ha : e a ∈ s <;> simp [ha, Function.comp_def]
    _ = _ := he.lintegral_comp (hr.indicator hs)

private theorem continuous_diagonalUnits {E : Type*} [Field E] [TopologicalSpace E]
    [IsTopologicalRing E] [ContinuousInv₀ E] (m : ℕ) :
    Continuous (Iwasawa.diagonalUnits : (Fin m → Eˣ) →
      Langlands.GeneralLinear m E) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun a : Fin m → Eˣ => Matrix.diagonal (fun i => (a i : E)))
    exact (continuous_pi fun i =>
      Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · change Continuous (fun a : Fin m → Eˣ =>
      Matrix.diagonal (fun i => (((a i)⁻¹ : Eˣ) : E)))
    exact (continuous_pi fun i =>
      Units.continuous_val.comp (continuous_inv.comp (continuous_apply i))).matrix_diagonal

/-- The actual quotient integral in cumulative-product root coordinates,
conditional only on the ordinary-diagonal Iwasawa measure identity. -/
theorem quotientRootIntegration {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    QuotientRootIntegrationStatement F T n := by
  classical
  intro hI
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : SecondCountableTopology F.Carrierˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  have : T2Space F.Carrier := inferInstance
  let A := Fin (n + 1) → F.Carrierˣ
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set G)
  have hκ : κ Set.univ = 1 := by
    change (generalLinearHaar F.Carrier n).restrict (K : Set G) Set.univ = 1
    rw [Measure.restrict_apply_univ]
    exact generalLinearHaar_integralSubgroup F.Carrier n
  let : IsFiniteMeasure κ := ⟨by rw [hκ]; exact ENNReal.one_lt_top⟩
  let ν := dA.prod κ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let e : A × G → A × G := Prod.map d id
  let q₀ : A × G → LeftUnipotentQuotient n F.Carrier := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
      (Iwasawa.diagonalUnits x.1 * x.2)
  let q := q₀ ∘ e
  let δ : A → ℝ := fun a =>
    ∏ i, ∏ j ∈ Finset.univ.filter (i < ·),
      T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier)
  let ρ : A → ℝ := fun a =>
    (∏ i, T.normalizedAbs (a i : F.Carrier) ^ ((i.val + 1) * (n - i.val)))⁻¹
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  have hd := rootCoordinateChange F T n
  have hdp : MeasurePreserving d dA dA :=
    ⟨hd.1.measurable, hd.2.2.2.2.2.1⟩
  have hep : MeasurePreserving e ν ν := hdp.prod (MeasurePreserving.id κ)
  have hq₀c : Continuous q₀ :=
    (leftQuotient_isOpenQuotientMap _).continuous.comp
      (((continuous_diagonalUnits (n + 1)).comp continuous_fst).mul continuous_snd)
  have hq₀ : Measurable q₀ := hq₀c.measurable
  have hq : Measurable q := hq₀.comp hep.measurable
  have hAbs : Continuous T.normalizedAbs :=
    NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
  have hδ : Continuous δ := by
    apply continuous_finsetProd
    intro i _
    apply continuous_finsetProd
    intro j _
    have hc : Continuous (fun a : A => ((a i / a j : F.Carrierˣ) : F.Carrier)) := by
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
  have hρ (a : A) : ρ a = (δ (d a))⁻¹ := by
    exact congrArg Inv.inv (hd.2.2.2.2.2.2 a).2.2.2.2.symm
  have hρpos (a : A) : 0 < ρ a := by rw [hρ]; exact inv_pos.mpr (hδpos _)
  have hρc : Continuous ρ := by
    have heq : ρ = fun a => (δ (d a))⁻¹ := funext hρ
    rw [heq]
    exact (hδ.comp hd.1).inv₀ (fun a => (hδpos _).ne')
  have hw (a : A) : w a = (ρ a : ℂ) := by
    simp only [w, ρ, Complex.ofReal_inv, Complex.ofReal_prod, Complex.ofReal_pow]
  let r₀ : A × G → ENNReal := fun x => ENNReal.ofReal ((δ x.1)⁻¹)
  let r : A × G → ENNReal := fun x => ENNReal.ofReal (ρ x.1)
  have hr₀ : Measurable r₀ :=
    (((hδ.inv₀ (fun a => (hδpos a).ne')).measurable).comp measurable_fst).ennreal_ofReal
  have hr : Measurable r := (hρc.measurable.comp measurable_fst).ennreal_ofReal
  have hre : r = r₀ ∘ e := by funext x; exact congrArg ENNReal.ofReal (hρ x.1)
  have hmap : Measure.map e (ν.withDensity r) = ν.withDensity r₀ := by
    rw [hre]
    exact map_density_comp hep hr₀
  dsimp only
  intro hright μ hμ
  have hμroot : μ = Measure.map q (ν.withDensity r) := by
    calc
      μ = Measure.map q₀ (ν.withDensity r₀) := hI μ hμ
      _ = Measure.map q₀ (Measure.map e (ν.withDensity r)) := by rw [hmap]
      _ = Measure.map q (ν.withDensity r) :=
        Measure.map_map hq₀ hep.measurable
  refine ⟨hμroot, ?_⟩
  intro f hf
  let H : A × G → ℂ := fun x => f (q x) * w x.1
  have hwm : Measurable w := by
    have heq : w = fun a => (ρ a : ℂ) := funext hw
    rw [heq]
    exact (Complex.continuous_ofReal.comp hρc).measurable
  have hH : Measurable H := (hf.comp hq).mul (hwm.comp measurable_fst)
  have hfinite : ∀ᵐ x ∂ν, r x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweighted : (fun x => (r x).toReal • (f ∘ q) x) = H := by
    funext x
    change (ENNReal.ofReal (ρ x.1)).toReal • f (q x) = f (q x) * w x.1
    rw [ENNReal.toReal_ofReal (hρpos x.1).le, hw, Complex.real_smul]
    exact mul_comm _ _
  have hint : Integrable f μ ↔ Integrable H ν := by
    rw [hμroot, integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable
      hq.aemeasurable, integrable_withDensity_iff_integrable_smul' hr hfinite, hweighted]
  constructor
  · rw [hint]
    change Integrable H (dA.prod κ) ↔ _
    rw [Integrable, hasFiniteIntegral_iff_enorm,
      lintegral_prod _ hH.enorm.aemeasurable]
    exact and_iff_right hH.stronglyMeasurable.aestronglyMeasurable
  · intro hi
    calc
      (∫ x, f x ∂μ) = ∫ x, (f ∘ q) x ∂ν.withDensity r := by
        rw [hμroot]
        exact integral_map hq.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable
      _ = ∫ x, H x ∂ν := by
        rw [integral_withDensity_eq_integral_toReal_smul hr hfinite, hweighted]
      _ = ∫ a, ∫ z, H (a, z) ∂κ ∂dA := integral_prod _ (hint.mp hi)

end Langlands.RankinSelberg
