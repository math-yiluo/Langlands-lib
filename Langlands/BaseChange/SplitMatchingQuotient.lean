import Langlands.BaseChange.SplitMatchingChart
import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.QuotientFactorization

/-! The split centralizer, quotient chart, and measure transport. -/

noncomputable section

open MeasureTheory Topology
open scoped CompactlySupported

namespace Langlands.BaseChange

open QuotientIntegration TraceFormula

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n l : ℕ}

local notation "G" => GeneralLinear n F
local notation "GE" => GeneralLinear n (Fin (l + 1) → F)
local notation "W" => Fin l → G
local notation "κ" => splitGLCoordinates F n (l + 1)
local notation "σ" => splitCyclicShift F (l + 1)
local notation "τ" => entrywiseAut σ n

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem continuous_splitEntrywiseAut : Continuous (τ : GE → GE) := by
  have he : (τ : GE → GE) = (κ).symm ∘
      (fun x : GE => fun i => κ x (finRotate (l + 1) i)) := by
    funext x
    apply (κ).injective
    rw [Function.comp_apply, ContinuousMulEquiv.apply_symm_apply]
    exact funext (splitGLCoordinates_shift F n (l + 1) x)
  rw [he]
  exact (κ).symm.continuous.comp (continuous_pi fun i =>
    (continuous_apply (finRotate (l + 1) i)).comp (κ).continuous)

theorem isClosed_splitCentralizer (δ : GE) : IsClosed (sigmaCentralizer σ n δ : Set GE) := by
  let := LocalFieldTopology.generalLinear_t2Space F n
  let : T2Space GE := (κ).toHomeomorph.isEmbedding.t2Space
  exact isClosed_eq ((continuous_inv.mul continuous_const).mul continuous_splitEntrywiseAut)
    continuous_const

theorem isClosed_glCentralizer (γ : G) : IsClosed (glCentralizer γ : Set G) := by
  let := LocalFieldTopology.generalLinear_t2Space F n
  rw [glCentralizer_eq_centralizer]
  exact Set.isClosed_centralizer {γ}

/-- The chart with the first coordinate translated by the associated conjugator. -/
def splitAmbientChart (δ : GE) (b : G) : GE ≃ₜ G × W :=
  ((κ).toHomeomorph.trans (splitCycleChart (κ δ))).trans
    ((Homeomorph.mulLeft b⁻¹).prodCongr (Homeomorph.refl W))

@[simp] theorem splitAmbientChart_fst (δ : GE) (b : G) (x : GE) :
    (splitAmbientChart δ b x).1 = b⁻¹ * κ x 0 :=
  congrArg (b⁻¹ * ·) (splitCycleChart_fst (κ δ) (κ x))

theorem splitAmbientChart_snd (δ : GE) (b : G) (x : GE) (i : Fin l) :
    (splitAmbientChart δ b x).2 i = κ (twistedConj τ x δ) i.castSucc := by
  change (splitCycleChart (κ δ) (κ x)).2 i = _
  rw [splitCycleChart_snd]
  simp only [twistedConj_apply, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply,
    splitGLCoordinates_shift, show finRotate (l + 1) i.castSucc = i.succ from
      finRotate_of_lt i.isLt]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem splitTwistedProduct (δ x : GE) :
    (List.ofFn (κ (twistedConj τ x δ))).prod =
      (κ x 0)⁻¹ * (List.ofFn (κ δ)).prod * κ x 0 := by
  have hperiod := (isCyclicAlgebra_splitCyclicShift F l).pow_eq_one
  rw [← splitGLCoordinates_norm_zero, twistedConj_apply, cyclicNorm_twistedConj,
    hperiod, entrywiseAut_one_apply, map_mul, map_mul, map_inv, Pi.mul_apply,
    Pi.mul_apply, Pi.inv_apply, splitGLCoordinates_norm_zero]

theorem splitAmbientChart_twistedConj (δ : GE) (b γ : G)
    (hγ : b⁻¹ * (List.ofFn (κ δ)).prod * b = γ) (x : GE) :
    κ (twistedConj τ x δ) =
      Fin.snoc (splitAmbientChart δ b x).2
        ((List.ofFn (splitAmbientChart δ b x).2).prod⁻¹ *
          ((splitAmbientChart δ b x).1⁻¹ * γ * (splitAmbientChart δ b x).1)) := by
  let d := κ (twistedConj τ x δ)
  have h := splitTwistedProduct δ x
  change (List.ofFn d).prod = _ at h
  have hs : (splitAmbientChart δ b x).2 = Fin.init d :=
    funext (splitAmbientChart_snd δ b x)
  change d = _
  rw [hs]
  rw [splitOrderedProduct_init_last] at h
  refine (Fin.snoc_init_self (q := d)).symm.trans
    (congrArg (@Fin.snoc l (fun _ => G) (Fin.init d)) ?_)
  rw [eq_inv_mul_iff_mul_eq, h, splitAmbientChart_fst, ← hγ]
  group

section Centralizer

variable (δ : GeneralLinear n (Fin (l + 1) → F)) (b γ : GeneralLinear n F)
  (hγ : b⁻¹ * (List.ofFn (splitGLCoordinates F n (l + 1) δ)).prod * b = γ)

local notation "C" => sigmaCentralizer (F := F) σ n δ
local notation "Z" => glCentralizer (F := F) (n := n) γ
local notation "T" => splitAmbientChart δ b

private def splitCentralizerForward (c : C) : Z :=
  ⟨b⁻¹ * κ c.val 0 * b, by
    have hc : twistedConj τ c.val δ = δ := c.property
    have hn := splitTwistedProduct δ c.val
    rw [hc] at hn
    change (b⁻¹ * κ c.val 0 * b)⁻¹ * γ * (b⁻¹ * κ c.val 0 * b) = γ
    calc
      _ = b⁻¹ * ((κ c.val 0)⁻¹ * (List.ofFn (κ δ)).prod * κ c.val 0) * b := by
        rw [← hγ]
        group
      _ = γ := by rw [← hn, hγ]⟩

private def splitCentralizerInverse (z : Z) : C :=
  ⟨(T).symm (z.val * b⁻¹, Fin.init (κ δ)), by
    change twistedConj τ ((T).symm (z.val * b⁻¹, Fin.init (κ δ))) δ = δ
    apply (κ).injective
    rw [splitAmbientChart_twistedConj δ b γ hγ, Homeomorph.apply_symm_apply]
    have hz : z.val⁻¹ * γ * z.val = γ := z.property
    have he : (z.val * b⁻¹)⁻¹ * γ * (z.val * b⁻¹) = (List.ofFn (κ δ)).prod := by
      calc
        _ = b * (z.val⁻¹ * γ * z.val) * b⁻¹ := by group
        _ = _ := by rw [hz, ← hγ]; group
    change @Fin.snoc l (fun _ => G) (Fin.init (κ δ))
      ((List.ofFn (Fin.init (κ δ))).prod⁻¹ * ((z.val * b⁻¹)⁻¹ * γ * (z.val * b⁻¹))) = κ δ
    rw [he, splitOrderedProduct_init_last (κ δ), inv_mul_cancel_left]
    exact Fin.snoc_init_self (κ δ)⟩

/-- Read the conjugated zeroth coordinate of a twisted centralizer element. -/
def splitCentralizerEquiv : C ≃ₜ* Z where
  toFun := splitCentralizerForward δ b γ hγ
  invFun := splitCentralizerInverse δ b γ hγ
  left_inv c := by
    apply Subtype.ext
    apply (T).injective
    change (T) ((T).symm ((splitCentralizerForward δ b γ hγ c).val * b⁻¹, Fin.init (κ δ))) =
      (T) c.val
    rw [Homeomorph.apply_symm_apply]
    apply Prod.ext
    · simp [splitCentralizerForward, mul_assoc]
    · funext i
      exact (splitAmbientChart_snd δ b c.val i).trans
        (congrArg (fun x : GE => κ x i.castSucc) c.property) |>.symm
  right_inv z := by
    apply Subtype.ext
    change b⁻¹ * κ ((T).symm (z.val * b⁻¹, Fin.init (κ δ))) 0 * b = z.val
    rw [← splitAmbientChart_fst, Homeomorph.apply_symm_apply]
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    change b⁻¹ * κ (x.val * y.val) 0 * b = (b⁻¹ * κ x.val 0 * b) * (b⁻¹ * κ y.val 0 * b)
    rw [map_mul, Pi.mul_apply]
    group
  continuous_toFun :=
    ((continuous_const.mul ((continuous_apply 0).comp
      ((κ).continuous.comp continuous_subtype_val))).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((T).symm.continuous.comp
      ((continuous_subtype_val.mul continuous_const).prodMk continuous_const)).subtype_mk _

theorem splitCentralizerEquiv_apply (c : C) :
    (splitCentralizerEquiv δ b γ hγ c).val = b⁻¹ * κ c.val 0 * b := rfl

theorem splitAmbientChart_left_mul (c : C) (x : GE) :
    (T) (c.val * x) = ((splitCentralizerEquiv δ b γ hγ c).val * ((T) x).1, ((T) x).2) := by
  apply Prod.ext
  · simp only [splitAmbientChart_fst, splitCentralizerEquiv_apply, map_mul, Pi.mul_apply]
    group
  · funext i
    simp only [splitAmbientChart_snd, twistedConj_apply, twistedConj_left_mul τ δ c x]

include hγ in
private def splitQuotientMap : LeftQuotient C → LeftQuotient Z × W :=
  descend C ((Prod.map (leftQuotientMap Z) id) ∘ (T)) (by
    intro c x
    simp only [Function.comp_apply, splitAmbientChart_left_mul δ b γ hγ]
    refine Prod.ext ((leftQuotient_mk_eq_mk_iff Z _ _).mpr ?_) rfl
    change ((T) x).1 * ((splitCentralizerEquiv δ b γ hγ c).val * ((T) x).1)⁻¹ ∈ Z
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    exact (Z).inv_mem (splitCentralizerEquiv δ b γ hγ c).property)

private theorem isHomeomorph_splitQuotientMap : IsHomeomorph (splitQuotientMap δ b γ hγ) := by
  have P : IsOpenQuotientMap (Prod.map (leftQuotientMap Z) (id : W → W)) :=
    (leftQuotient_isOpenQuotientMap Z).prodMap (IsOpenQuotientMap.id (X := W))
  have hcomp : (splitQuotientMap δ b γ hγ) ∘ leftQuotientMap C =
      Prod.map (leftQuotientMap Z) id ∘ (T) := rfl
  refine ⟨(leftQuotient_isOpenQuotientMap C).isQuotientMap.continuous_iff.mpr
    (by rw [hcomp]; exact P.continuous.comp (T).continuous), ?_, ?_, ?_⟩
  · apply IsOpenMap.of_comp (leftQuotient_isOpenQuotientMap C).continuous
      (leftQuotient_isOpenQuotientMap C).surjective
    rw [hcomp]
    exact P.isOpenMap.comp (T).isOpenMap
  · intro q r
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        intro hxy
        have hz : ((T) y).1 * ((T) x).1⁻¹ ∈ Z :=
          (leftQuotient_mk_eq_mk_iff Z _ _).mp (congrArg Prod.fst hxy)
        let z : Z := ⟨_, hz⟩
        let c := (splitCentralizerEquiv δ b γ hγ).symm z
        have hy : y = c.val * x := by
          apply (T).injective
          change (T) y = (T) (((splitCentralizerEquiv δ b γ hγ).symm z).val * x)
          rw [splitAmbientChart_left_mul δ b γ hγ, ContinuousMulEquiv.apply_symm_apply]
          refine Prod.ext ?_ (congrArg Prod.snd hxy).symm
          simp [z, mul_assoc]
        apply (leftQuotient_mk_eq_mk_iff C _ _).mpr
        simp [hy, mul_assoc]
  · intro p
    obtain ⟨q, hq⟩ := P.surjective p
    refine ⟨leftQuotientMap C ((T).symm q), ?_⟩
    change (splitQuotientMap δ b γ hγ ∘ leftQuotientMap C) ((T).symm q) = p
    rw [hcomp, Function.comp_apply, Homeomorph.apply_symm_apply, hq]

include hγ in
/-- On the left quotient the first coordinate becomes an ordinary coset. -/
def splitQuotientChart : LeftQuotient C ≃ₜ LeftQuotient Z × W :=
  (isHomeomorph_splitQuotientMap δ b γ hγ).homeomorph _

@[simp] theorem splitQuotientChart_mk (x : GE) :
    splitQuotientChart δ b γ hγ (leftQuotientMap C x) =
      (leftQuotientMap Z ((T) x).1, ((T) x).2) :=
  rfl

end Centralizer

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem splitAssociatedNorm_coordinate (δ : GE) (γ : G) (a : GE)
    (ha : a⁻¹ * cyclicNorm σ (l + 1) δ * a = baseChange F (Fin (l + 1) → F) n γ) :
    (κ a 0)⁻¹ * (List.ofFn (κ δ)).prod * κ a 0 = γ := by
  simpa only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, splitGLCoordinates_norm_zero,
    splitGLCoordinates_baseChange] using congrArg (fun x : GE => κ x 0) ha

section Measures

variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n (Fin (l + 1) → F))]
  [BorelSpace (GeneralLinear n (Fin (l + 1) → F))]

theorem splitAmbientChart_measurePreserving (δ : GE) (b : G)
    (μF : Measure G) [μF.IsHaarMeasure] (μE : Measure GE) [μE.IsHaarMeasure]
    (hμ : IsSplitProductHaar μF μE) :
    MeasurePreserving (splitAmbientChart δ b) μE (μF.prod (Measure.pi fun _ : Fin l => μF)) := by
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  exact ((measurePreserving_mul_left μF b⁻¹).prod
    (MeasurePreserving.id (Measure.pi fun _ : Fin l => μF))).comp
    ((splitCycleChart_measurePreserving μF (κ δ)).comp
      (splitGLCoordinates_measurePreserving μF μE hμ))

theorem splitCentralizerEquiv_measurePreserving (δ : GE) (γ : G) (a : GE)
    (hγ : (κ a 0)⁻¹ * (List.ofFn (κ δ)).prod * κ a 0 = γ)
    (μδ : Measure (sigmaCentralizer σ n δ)) (μγ : Measure (glCentralizer γ))
    (ha : Measure.map (fun c : sigmaCentralizer σ n δ => a⁻¹ * c.val * a) μδ =
      Measure.map (fun z : glCentralizer γ => baseChange F (Fin (l + 1) → F) n z.val) μγ) :
    MeasurePreserving (splitCentralizerEquiv δ (κ a 0) γ hγ) μδ μγ := by
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let e := splitCentralizerEquiv δ (κ a 0) γ hγ
  refine ⟨e.continuous.measurable, ?_⟩
  have hcoord : Measurable (fun x : GE => κ x 0) :=
    ((continuous_apply 0).comp (κ).continuous).measurable
  have hbase : Continuous (baseChange F (Fin (l + 1) → F) n : G → GE) := by
    have he : (baseChange F (Fin (l + 1) → F) n : G → GE) =
        (κ).symm ∘ (fun g : G => fun _ : Fin (l + 1) => g) := by
      funext g
      apply (κ).injective
      rw [Function.comp_apply, ContinuousMulEquiv.apply_symm_apply]
      exact funext (splitGLCoordinates_baseChange F n (l + 1) g)
    rw [he]
    exact (κ).symm.continuous.comp (continuous_pi fun _ => continuous_id)
  have hm := congrArg (Measure.map (fun x : GE => κ x 0)) ha
  have hsub : Measurable (fun z : glCentralizer γ =>
      baseChange F (Fin (l + 1) → F) n z.val) :=
    (hbase.comp continuous_subtype_val).measurable
  rw [Measure.map_map hcoord (by fun_prop), Measure.map_map hcoord hsub] at hm
  apply (MeasurableEmbedding.subtype_coe (isClosed_glCentralizer γ).measurableSet).map_injective
  have he : Measurable (e : sigmaCentralizer σ n δ → glCentralizer γ) := e.continuous.measurable
  change Measure.map Subtype.val (Measure.map e μδ) = Measure.map Subtype.val μγ
  rw [Measure.map_map measurable_subtype_coe he]
  simpa only [Function.comp_def, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply,
    splitGLCoordinates_baseChange, e, splitCentralizerEquiv_apply] using hm

/-- The inverse quotient chart takes the ordinary quotient measure times the free Haar
coordinates to the twisted quotient measure. -/
theorem splitQuotientChart_symm_measurePreserving (δ : GE) (b γ : G)
    (hγ : b⁻¹ * (List.ofFn (κ δ)).prod * b = γ)
    {μF : Measure G} [μF.IsHaarMeasure] {μE : Measure GE} [μE.IsHaarMeasure]
    (hμ : IsSplitProductHaar μF μE)
    {μδ : Measure (sigmaCentralizer σ n δ)} [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
    {μγ : Measure (glCentralizer γ)} [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    {νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))}
    {νγ : Measure (LeftQuotient (glCentralizer γ))}
    (hνδ : IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ)
    (hνγ : IsCompatible (glCentralizer γ) μF μγ νγ)
    (he : MeasurePreserving (splitCentralizerEquiv δ b γ hγ) μδ μγ) :
    MeasurePreserving (splitQuotientChart δ b γ hγ).symm
      (νγ.prod (Measure.pi fun _ : Fin l => μF)) νδ := by
  let C := sigmaCentralizer σ n δ
  let Z := glCentralizer γ
  let T := splitAmbientChart δ b
  let Θ := splitQuotientChart δ b γ hγ
  let e := splitCentralizerEquiv δ b γ hγ
  let ρ : Measure W := Measure.pi fun _ => μF
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : T2Space GE := (κ).toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace GE := (κ).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology GE := (κ).toHomeomorph.isEmbedding.secondCountableTopology
  have hC : IsClosed (C : Set GE) := isClosed_splitCentralizer δ
  have hZ : IsClosed (Z : Set G) := isClosed_glCentralizer γ
  let : T2Space (LeftQuotient C) := leftQuotient_t2Space C hC
  let : T2Space (LeftQuotient Z) := leftQuotient_t2Space Z hZ
  let := leftQuotient_locallyCompactSpace C
  let := leftQuotient_locallyCompactSpace Z
  let := (leftQuotient_isOpenQuotientMap Z).secondCountableTopology
  let : LocallyCompactSpace (sigmaCentralizer σ n δ) :=
    hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace G := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (sigmaCentralizer σ n δ) :=
    (hZ.isClosedEmbedding_subtypeVal.isEmbedding.comp
      e.toHomeomorph.isEmbedding).isInducing.pseudoMetrizableSpace
  let : μδ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let : νδ.Regular := hνδ.regular
  let : νγ.Regular := hνγ.regular
  let : IsFiniteMeasureOnCompacts ρ := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin l => μF))
  let : IsLocallyFiniteMeasure (νγ.prod ρ) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (LeftQuotient (glCentralizer γ) × W) := inferInstance
  let : SigmaCompactSpace (LeftQuotient (glCentralizer γ) × W) := inferInstance
  let : (νγ.prod ρ).Regular := inferInstance
  let : (Measure.map Θ.symm (νγ.prod ρ)).Regular := Measure.Regular.map Θ.symm
  change MeasurePreserving Θ.symm (νγ.prod ρ) νδ
  refine ⟨Θ.symm.continuous.measurable, ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨f, hf, -⟩ := realQuotientPositiveLifting C hC μδ φ
  have hf' (q : LeftQuotient C) : quotientAverageReal C μδ f q = φ q := by
    induction q using Quotient.inductionOn with
    | h x => exact hf x
  have havg (q : LeftQuotient Z) (w : W) :
      φ (Θ.symm (q, w)) = quotientAverageReal Z μγ (fun y => f (T.symm (y, w))) q := by
    induction q using Quotient.inductionOn with
    | h y =>
      let x := T.symm (y, w)
      have hx : Θ (leftQuotientMap C x) = (leftQuotientMap Z y, w) := by
        change splitQuotientChart δ b γ hγ (leftQuotientMap C x) = _
        rw [splitQuotientChart_mk]
        change (leftQuotientMap Z (T x).1, (T x).2) = _
        rw [show T x = (y, w) from T.apply_symm_apply _]
      change φ (Θ.symm (leftQuotientMap Z y, w)) = _
      rw [← hx, Homeomorph.symm_apply_apply, ← hf']
      change (∫ c : C, f (c.val * x) ∂μδ) = ∫ z : Z, f (T.symm (z.val * y, w)) ∂μγ
      have hc (c : C) : c.val * x = T.symm ((e c).val * y, w) := by
        apply T.injective
        rw [Homeomorph.apply_symm_apply]
        change splitAmbientChart δ b (c.val * x) = _
        rw [splitAmbientChart_left_mul δ b γ hγ]
        change ((e c).val * (T x).1, (T x).2) = _
        rw [show T x = (y, w) from T.apply_symm_apply _]
      simp_rw [hc]
      exact he.integral_comp e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun z : Z => f (T.symm (z.val * y, w)))
  have hslice (w : W) : HasCompactSupport (fun y : G => f (T.symm (y, w))) := by
    have h : IsClosedEmbedding (fun y : G => (y, w)) :=
      ⟨isEmbedding_prodMkLeft w, by
        rw [show Set.range (fun y : G => (y, w)) = Prod.snd ⁻¹' {w} by
          ext p
          rcases p with ⟨y, z⟩
          simp [eq_comm]]
        exact isClosed_singleton.preimage continuous_snd⟩
    exact f.hasCompactSupport.comp_isClosedEmbedding (T.symm.isClosedEmbedding.comp h)
  have hint : Integrable (fun p : G × W => f (T.symm p)) (μF.prod ρ) :=
    (f.continuous.comp T.symm.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph T.symm)
  have hT := splitAmbientChart_measurePreserving δ b μF μE hμ
  calc
    (∫ q, φ q ∂Measure.map Θ.symm (νγ.prod ρ)) = ∫ p, φ (Θ.symm p) ∂νγ.prod ρ :=
      integral_map_equiv Θ.symm.toMeasurableEquiv φ
    _ = ∫ w, ∫ q, φ (Θ.symm (q, w)) ∂νγ ∂ρ :=
      integral_prod_symm _ ((φ.continuous.comp Θ.symm.continuous).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.comp_homeomorph Θ.symm))
    _ = ∫ w, ∫ y, f (T.symm (y, w)) ∂μF ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        simp_rw [havg]
        exact hνγ.integral_quotientAverageReal _ (by fun_prop) (hslice w)
    _ = ∫ p, f (T.symm p) ∂μF.prod ρ := (integral_prod_symm _ hint).symm
    _ = ∫ x, f x ∂μE := hT.symm T.toMeasurableEquiv |>.integral_comp
      T.symm.toMeasurableEquiv.measurableEmbedding f
    _ = ∫ q, quotientAverageReal C μδ f q ∂νδ :=
      (hνδ.integral_quotientAverageReal f f.continuous f.hasCompactSupport).symm
    _ = ∫ q, φ q ∂νδ := by simp_rw [hf']

end Measures

end Langlands.BaseChange
