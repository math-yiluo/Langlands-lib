import Langlands.BaseChange.SplitMatchingChart
import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.QuotientAutomorphismProof

/-! # Quotient coordinates for a cycle with a twist at the last coordinate -/

noncomputable section

open MeasureTheory Topology
open scoped BigOperators CompactlySupported

namespace Langlands.BaseChange

open QuotientIntegration TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

variable {H : Type u} [Group H] [TopologicalSpace H]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {m : ℕ}
variable (κ : H ≃ₜ* (Fin (m + 1) → G)) (σ : H →* H) (τ : G →* G)

local notation "W" => Fin m → G

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem consecutiveProduct {k : ℕ} (d : Fin k → G) (x : Fin (k + 1) → G) :
    (List.ofFn (fun i : Fin k ↦ (x i.castSucc)⁻¹ * d i * x i.succ)).prod =
      (x 0)⁻¹ * (List.ofFn d).prod * x (Fin.last k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
      have h := ih (Fin.tail d) (Fin.tail x)
      simp only [Fin.tail, Fin.succ_last] at h
      have hindices (i : Fin k) : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      simp_rw [hindices]
      rw [h]
      change (x 0)⁻¹ * d 0 * x (Fin.succ 0) *
          ((x (Fin.succ 0))⁻¹ * (List.ofFn (Fin.tail d)).prod * x (Fin.last (k + 1))) =
        (x 0)⁻¹ * (d 0 * (List.ofFn (Fin.tail d)).prod) * x (Fin.last (k + 1))
      group

variable
  (hshift : ∀ (x : H) (i : Fin m), κ (σ x) i.castSucc = κ x i.succ)
  (hwrap : ∀ x : H, κ (σ x) (Fin.last m) = τ (κ x 0))

/-- Retain the first component and the nonfinal components of the twisted conjugate. -/
def cyclicProductAmbientChart (δ : H) : H ≃ₜ G × W :=
  κ.toHomeomorph.trans (splitCycleChart (κ δ))

@[simp]
theorem cyclicProductAmbientChart_fst (δ x : H) :
    (cyclicProductAmbientChart κ δ x).1 = κ x 0 :=
  splitCycleChart_fst (κ δ) (κ x)

include hshift in
theorem cyclicProductAmbientChart_snd (δ x : H) (i : Fin m) :
    (cyclicProductAmbientChart κ δ x).2 i = κ (twistedConj σ x δ) i.castSucc := by
  change (splitCycleChart (κ δ) (κ x)).2 i = _
  rw [splitCycleChart_snd]
  simp only [twistedConj_apply, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hshift]

include hshift hwrap in
omit [IsTopologicalGroup G] in
/-- The ordered product of the components transforms by twisted conjugation in the
first component, with the wraparound twist. -/
theorem orderedProduct_twistedConj (δ x : H) :
    (List.ofFn (κ (twistedConj σ x δ))).prod =
      twistedConj τ (κ x 0) (List.ofFn (κ δ)).prod := by
  let x' : Fin (m + 2) → G := Fin.snoc (κ x) (τ (κ x 0))
  have hcoord (i : Fin (m + 1)) :
      κ (twistedConj σ x δ) i = (x' i.castSucc)⁻¹ * κ δ i * x' i.succ := by
    simp only [x', Fin.snoc_castSucc, twistedConj_apply, map_mul, map_inv,
      Pi.mul_apply, Pi.inv_apply]
    induction i using Fin.lastCases with
    | last => rw [hwrap, Fin.succ_last, Fin.snoc_last]
    | cast i => rw [hshift, ← Fin.castSucc_succ, Fin.snoc_castSucc]
  rw [funext hcoord, consecutiveProduct]
  rw [show x' 0 = κ x 0 from Fin.snoc_apply_zero _ _,
    show x' (Fin.last (m + 1)) = τ (κ x 0) from Fin.snoc_last _ _]
  rfl

include hshift hwrap in
theorem cyclicProductAmbientChart_twistedConj (δ x : H) :
    κ (twistedConj σ x δ) =
      Fin.snoc (cyclicProductAmbientChart κ δ x).2
        ((List.ofFn (cyclicProductAmbientChart κ δ x).2).prod⁻¹ *
          twistedConj τ (cyclicProductAmbientChart κ δ x).1 (List.ofFn (κ δ)).prod) := by
  let d := κ (twistedConj σ x δ)
  have h := orderedProduct_twistedConj κ σ τ hshift hwrap δ x
  change (List.ofFn d).prod = _ at h
  have hs : (cyclicProductAmbientChart κ δ x).2 = Fin.init d :=
    funext (cyclicProductAmbientChart_snd κ σ hshift δ x)
  rw [hs, cyclicProductAmbientChart_fst]
  change d = _
  rw [splitOrderedProduct_init_last] at h
  refine (Fin.snoc_init_self (q := d)).symm.trans
    (congrArg (Fin.snoc (Fin.init d)) ?_)
  rw [← h, inv_mul_cancel_left]

section Centralizers

variable (δ : H)

local notation "C" => twistedCentralizer σ δ
local notation "Z" => twistedCentralizer τ (List.prod (List.ofFn (κ δ)))
local notation "T" => cyclicProductAmbientChart κ δ

include hshift hwrap in
private def cyclicProductCentralizerForward (c : C) : Z :=
  ⟨κ c.val 0, by
    change twistedConj τ (κ c.val 0) (List.ofFn (κ δ)).prod = _
    have hc : twistedConj σ c.val δ = δ := c.property
    rw [← orderedProduct_twistedConj κ σ τ hshift hwrap, hc]⟩

include hshift hwrap in
private def cyclicProductCentralizerInverse (z : Z) : C :=
  ⟨(T).symm (z.val, Fin.init (κ δ)), by
    change twistedConj σ ((T).symm (z.val, Fin.init (κ δ))) δ = δ
    apply κ.injective
    rw [cyclicProductAmbientChart_twistedConj κ σ τ hshift hwrap, Homeomorph.apply_symm_apply]
    change Fin.snoc (Fin.init (κ δ))
      ((List.ofFn (Fin.init (κ δ))).prod⁻¹ *
        twistedConj τ z.val (List.ofFn (κ δ)).prod) = κ δ
    have hz : twistedConj τ z.val (List.ofFn (κ δ)).prod = (List.ofFn (κ δ)).prod :=
      z.property
    rw [hz, splitOrderedProduct_init_last (κ δ), inv_mul_cancel_left]
    exact Fin.snoc_init_self (κ δ)⟩

include hshift hwrap in
/-- The zeroth coordinate identifies the twisted centralizers. -/
def cyclicProductCentralizerEquiv : C ≃ₜ* Z where
  toFun := cyclicProductCentralizerForward κ σ τ hshift hwrap δ
  invFun := cyclicProductCentralizerInverse κ σ τ hshift hwrap δ
  left_inv c := by
    apply Subtype.ext
    apply (T).injective
    change T ((T).symm (κ c.val 0, Fin.init (κ δ))) = T c.val
    rw [Homeomorph.apply_symm_apply]
    refine Prod.ext (cyclicProductAmbientChart_fst κ δ c.val).symm ?_
    funext i
    have hc : twistedConj σ c.val δ = δ := c.property
    rw [cyclicProductAmbientChart_snd κ σ hshift, hc]
    rfl
  right_inv z := by
    apply Subtype.ext
    change κ ((T).symm (z.val, Fin.init (κ δ))) 0 = _
    rw [← cyclicProductAmbientChart_fst κ δ, Homeomorph.apply_symm_apply]
  map_mul' c d := by
    apply Subtype.ext
    change κ (c.val * d.val) 0 = κ c.val 0 * κ d.val 0
    rw [map_mul, Pi.mul_apply]
  continuous_toFun :=
    ((continuous_apply 0).comp (κ.continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((T).symm.continuous.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

include hshift hwrap in
@[simp]
theorem cyclicProductCentralizerEquiv_apply (c : C) :
    (cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ c).val = κ c.val 0 := rfl

include hshift hwrap in
theorem cyclicProductAmbientChart_left_mul (c : C) (x : H) :
    T (c.val * x) = ((cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ c).val *
      (T x).1, (T x).2) := by
  refine Prod.ext ?_ ?_
  · simp only [cyclicProductAmbientChart_fst, cyclicProductCentralizerEquiv_apply,
      map_mul, Pi.mul_apply]
  · funext i
    simp only [cyclicProductAmbientChart_snd κ σ hshift]
    exact congrArg (fun y : H ↦ κ y i.castSucc) (twistedConj_left_mul σ δ c x)

variable [IsTopologicalGroup H]

local notation "e" => cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ

include hshift hwrap in
private def cyclicProductQuotientMap : LeftQuotient C → LeftQuotient Z × W :=
  descend C ((Prod.map (leftQuotientMap Z) id) ∘ T) (by
    intro c x
    rw [Function.comp_apply, cyclicProductAmbientChart_left_mul κ σ τ hshift hwrap]
    refine Prod.ext ((leftQuotient_mk_eq_mk_iff Z _ _).mpr ?_) rfl
    change ((T) x).1 * ((e c).val * ((T) x).1)⁻¹ ∈ Z
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    exact (Z).inv_mem (e c).property)

include hshift hwrap in
private theorem isHomeomorph_cyclicProductQuotientMap :
    IsHomeomorph (cyclicProductQuotientMap κ σ τ hshift hwrap δ) := by
  let qC := leftQuotientMap C
  let qZ := Prod.map (leftQuotientMap Z) (id : W → W)
  let q := cyclicProductQuotientMap κ σ τ hshift hwrap δ
  have hC := leftQuotient_isOpenQuotientMap C
  have hZ := (leftQuotient_isOpenQuotientMap Z).prodMap (IsOpenQuotientMap.id (X := W))
  have hcomp : q ∘ qC = qZ ∘ T := rfl
  refine ⟨hC.isQuotientMap.continuous_iff.mpr ?_, ?_, ?_, ?_⟩
  · rw [hcomp]
    exact hZ.continuous.comp (T).continuous
  · apply IsOpenMap.of_comp hC.continuous hC.surjective
    rw [hcomp]
    exact hZ.isOpenMap.comp (T).isOpenMap
  · intro a b
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        intro hxy
        have hz : ((T) y).1 * ((T) x).1⁻¹ ∈ Z :=
          (leftQuotient_mk_eq_mk_iff Z _ _).mp (congrArg Prod.fst hxy)
        let z : Z := ⟨_, hz⟩
        let c := (e).symm z
        have heq : y = c.val * x := by
          apply (T).injective
          rw [cyclicProductAmbientChart_left_mul κ σ τ hshift hwrap,
            show e c = z from (e).apply_symm_apply z]
          refine Prod.ext ?_ (congrArg Prod.snd hxy).symm
          simp [z, mul_assoc]
        apply (leftQuotient_mk_eq_mk_iff C _ _).mpr
        simp [heq, mul_assoc]
  · intro p
    obtain ⟨a, ha⟩ := hZ.surjective p
    refine ⟨qC ((T).symm a), ?_⟩
    change (q ∘ qC) ((T).symm a) = p
    rw [hcomp, Function.comp_apply, Homeomorph.apply_symm_apply]
    exact ha

include hshift hwrap in
/-- The quotient for a cyclic product is the twisted quotient on one factor times the
remaining free group coordinates. -/
def cyclicProductQuotientChart : LeftQuotient C ≃ₜ LeftQuotient Z × W :=
  (isHomeomorph_cyclicProductQuotientMap κ σ τ hshift hwrap δ).homeomorph _

include hshift hwrap in
@[simp]
theorem cyclicProductQuotientChart_mk (x : H) :
    cyclicProductQuotientChart κ σ τ hshift hwrap δ (leftQuotientMap C x) =
      (leftQuotientMap Z ((T) x).1, ((T) x).2) := rfl

end Centralizers

section Measures

variable [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable (δ : H)

local notation "C" => twistedCentralizer σ δ
local notation "Z" => twistedCentralizer τ (List.prod (List.ofFn (κ δ)))
local notation "T" => cyclicProductAmbientChart κ δ
local notation "e" => cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ
local notation "Θ" => cyclicProductQuotientChart κ σ τ hshift hwrap δ

include hshift hwrap in
/-- The inverse quotient chart carries the product of the factor quotient measure and
the free Haar measures to the supplied compatible product-side quotient measure. -/
theorem cyclicProductQuotientChart_symm_measurePreserving
    (hσ : Continuous σ) (hτ : Continuous τ)
    {μ : Measure G} [μ.IsHaarMeasure] {μH : Measure H}
    (hκ : MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) ↦ μ))
    {μC : Measure C} [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
    {μZ : Measure Z} [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
    {νC : Measure (LeftQuotient C)} {νZ : Measure (LeftQuotient Z)}
    (hνC : IsCompatible C μH μC νC) (hνZ : IsCompatible Z μ μZ νZ)
    (he : MeasurePreserving e μC μZ) :
    MeasurePreserving (Θ).symm (νZ.prod (Measure.pi fun _ : Fin m ↦ μ)) νC := by
  let ρ : Measure W := Measure.pi fun _ ↦ μ
  let : T2Space H := κ.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace H := κ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology H := κ.toHomeomorph.isEmbedding.secondCountableTopology
  have hC : IsClosed (C : Set H) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hσ) continuous_const
  have hZ : IsClosed (Z : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hτ) continuous_const
  let : T2Space (LeftQuotient C) := leftQuotient_t2Space C hC
  let : T2Space (LeftQuotient Z) := leftQuotient_t2Space Z hZ
  let := leftQuotient_locallyCompactSpace C
  let := leftQuotient_locallyCompactSpace Z
  let := (leftQuotient_isOpenQuotientMap Z).secondCountableTopology
  let : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace C :=
    (hZ.isClosedEmbedding_subtypeVal.isEmbedding.comp
      (e).toHomeomorph.isEmbedding).isInducing.pseudoMetrizableSpace
  let : μC.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let : νC.Regular := hνC.regular
  let : νZ.Regular := hνZ.regular
  let : IsFiniteMeasureOnCompacts ρ := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin m ↦ μ))
  let : IsLocallyFiniteMeasure (νZ.prod ρ) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (LeftQuotient Z × W) := inferInstance
  let : SigmaCompactSpace (LeftQuotient Z × W) := inferInstance
  let : (νZ.prod ρ).Regular := inferInstance
  let : (Measure.map (Θ).symm (νZ.prod ρ)).Regular := Measure.Regular.map (Θ).symm
  refine ⟨(Θ).symm.continuous.measurable, ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨f, hf, -⟩ := realQuotientPositiveLifting C hC μC φ
  have hf' (q : LeftQuotient C) : quotientAverageReal C μC f q = φ q := by
    induction q using Quotient.inductionOn with
    | h x => exact hf x
  have havg (q : LeftQuotient Z) (w : W) :
      φ ((Θ).symm (q, w)) = quotientAverageReal Z μZ (fun y ↦ f ((T).symm (y, w))) q := by
    induction q using Quotient.inductionOn with
    | h y =>
      let x := (T).symm (y, w)
      have hTx : T x = (y, w) := (T).apply_symm_apply _
      have hx : Θ (leftQuotientMap C x) = (leftQuotientMap Z y, w) := by
        rw [cyclicProductQuotientChart_mk, hTx]
      change φ ((Θ).symm (leftQuotientMap Z y, w)) = _
      rw [← hx, Homeomorph.symm_apply_apply, ← hf']
      change (∫ c : C, f (c.val * x) ∂μC) =
        ∫ z : Z, f ((T).symm (z.val * y, w)) ∂μZ
      have hc (c : C) : c.val * x = (T).symm ((e c).val * y, w) := by
        apply (T).injective
        rw [Homeomorph.apply_symm_apply, cyclicProductAmbientChart_left_mul κ σ τ hshift hwrap,
          hTx]
      simp_rw [hc]
      exact he.integral_comp (e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun z : Z ↦ f ((T).symm (z.val * y, w)))
  have hslice (w : W) : HasCompactSupport (fun y : G ↦ f ((T).symm (y, w))) := by
    have hc : IsClosedEmbedding (fun y : G ↦ (y, w)) :=
      ⟨isEmbedding_prodMkLeft w, by
        rw [show Set.range (fun y : G ↦ (y, w)) = Prod.snd ⁻¹' {w} by
          ext p
          rcases p with ⟨y, z⟩
          simp [eq_comm]]
        exact isClosed_singleton.preimage continuous_snd⟩
    exact f.hasCompactSupport.comp_isClosedEmbedding ((T).symm.isClosedEmbedding.comp hc)
  have hint : Integrable (fun p : G × W ↦ f ((T).symm p)) (μ.prod ρ) :=
    (f.continuous.comp (T).symm.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph (T).symm)
  have hT : MeasurePreserving T μH (μ.prod ρ) :=
    (splitCycleChart_measurePreserving μ (κ δ)).comp hκ
  calc
    (∫ q, φ q ∂Measure.map (Θ).symm (νZ.prod ρ)) = ∫ p, φ ((Θ).symm p) ∂νZ.prod ρ :=
      integral_map_equiv (Θ).symm.toMeasurableEquiv φ
    _ = ∫ w, ∫ q, φ ((Θ).symm (q, w)) ∂νZ ∂ρ :=
      integral_prod_symm _ ((φ.continuous.comp (Θ).symm.continuous).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.comp_homeomorph (Θ).symm))
    _ = ∫ w, ∫ y, f ((T).symm (y, w)) ∂μ ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦ by
        simp_rw [havg]
        exact hνZ.integral_quotientAverageReal _ (by fun_prop) (hslice w)
    _ = ∫ p, f ((T).symm p) ∂μ.prod ρ := (integral_prod_symm _ hint).symm
    _ = ∫ x, f x ∂μH := hT.symm (T).toMeasurableEquiv |>.integral_comp
      (T).symm.toMeasurableEquiv.measurableEmbedding f
    _ = ∫ q, quotientAverageReal C μC f q ∂νC :=
      (hνC.integral_quotientAverageReal f f.continuous f.hasCompactSupport).symm
    _ = ∫ q, φ q ∂νC := by simp_rw [hf']

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] in
private theorem snoc_inv_prod_mem_iff (K : Subgroup G) (w : W) (y : G) :
    (∀ i, @Fin.snoc m (fun _ ↦ G) w ((List.ofFn w).prod⁻¹ * y) i ∈ K) ↔
      (∀ i, w i ∈ K) ∧ y ∈ K := by
  have hprod (hw : ∀ i, w i ∈ K) : (List.ofFn w).prod ∈ K := by
    apply K.list_prod_mem
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hw i
  constructor
  · intro h
    have hw (i : Fin m) := h i.castSucc
    simp only [Fin.snoc_castSucc] at hw
    have hy := h (Fin.last m)
    rw [Fin.snoc_last] at hy
    exact ⟨hw, by simpa using K.mul_mem (hprod hw) hy⟩
  · rintro ⟨hw, hy⟩ i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact K.mul_mem (K.inv_mem (hprod hw)) hy
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact hw i

include hshift hwrap in
/-- For normalized subgroup indicators on a cyclic product, the free coordinates
integrate to one, leaving the twisted orbital integral on the first factor. -/
theorem cyclicProductUnitOrbitalIntegral_eq
    (hσ : Continuous σ) (hτ : Continuous τ)
    {μ : Measure G} [μ.IsHaarMeasure] {μH : Measure H}
    (hκ : MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) ↦ μ))
    {μC : Measure C} [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
    {μZ : Measure Z} [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
    {νC : Measure (LeftQuotient C)} {νZ : Measure (LeftQuotient Z)}
    (hνC : IsCompatible C μH μC νC) (hνZ : IsCompatible Z μ μZ νZ)
    (he : MeasurePreserving e μC μZ)
    (K : Subgroup G) (hK : MeasurableSet (K : Set G)) (hvol : μ K = 1) :
    twistedOrbitalIntegral σ δ νC (fun x ↦ (Set.pi Set.univ
      (fun _ : Fin (m + 1) ↦ (K : Set G))).indicator (fun _ ↦ 1) (κ x)) =
    twistedOrbitalIntegral τ (List.ofFn (κ δ)).prod νZ ((K : Set G).indicator (fun _ ↦ 1)) := by
  classical
  let := leftQuotient_locallyCompactSpace Z
  let := (leftQuotient_isOpenQuotientMap Z).secondCountableTopology
  let : νZ.Regular := hνZ.regular
  let ρ : Measure W := Measure.pi fun _ ↦ μ
  let unitTail : W → ℂ :=
    (Set.pi Set.univ fun _ : Fin m ↦ (K : Set G)).indicator (fun _ ↦ 1)
  let unitProduct : H → ℂ := fun x ↦ (Set.pi Set.univ
    (fun _ : Fin (m + 1) ↦ (K : Set G))).indicator (fun _ ↦ 1) (κ x)
  let unitFactor : G → ℂ := (K : Set G).indicator (fun _ ↦ 1)
  let f := twistedOrbitFunction σ δ unitProduct
  let g := twistedOrbitFunction τ (List.ofFn (κ δ)).prod unitFactor
  have hΘ := cyclicProductQuotientChart_symm_measurePreserving
    κ σ τ hshift hwrap δ hσ hτ hκ hνC hνZ he
  have heval (q : LeftQuotient C) : f q = g (Θ q).1 * unitTail (Θ q).2 := by
    induction q using Quotient.inductionOn with
    | h x =>
      change unitProduct (twistedConj σ x δ) =
        unitFactor (twistedConj τ ((T) x).1 (List.ofFn (κ δ)).prod) * unitTail ((T) x).2
      simp only [unitProduct, unitFactor, unitTail, cyclicProductAmbientChart_twistedConj κ σ τ
        hshift hwrap, Set.indicator_apply, Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe,
        snoc_inv_prod_mem_iff]
      by_cases hw : ∀ i, ((T) x).2 i ∈ K <;> simp [hw]
  have hmass : ∫ w, unitTail w ∂ρ = 1 := by
    have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin m ↦ (K : Set G)) :=
      MeasurableSet.pi Set.countable_univ (fun _ _ ↦ hK)
    have hπ : ρ (Set.pi Set.univ fun _ : Fin m ↦ (K : Set G)) = 1 := by
      simp [ρ, Measure.pi_pi, hvol]
    change (∫ w : W, (Set.pi Set.univ fun _ : Fin m ↦ (K : Set G)).indicator
      (fun _ ↦ (1 : ℂ)) w ∂ρ) = 1
    rw [integral_indicator_const _ hmeas]
    simp [measureReal_def, hπ]
  change (∫ q, f q ∂νC) = ∫ q, g q ∂νZ
  calc
    _ = ∫ p, f ((Θ).symm p) ∂νZ.prod ρ :=
      (hΘ.integral_comp (Θ).symm.toMeasurableEquiv.measurableEmbedding f).symm
    _ = ∫ p, g p.1 * unitTail p.2 ∂νZ.prod ρ := by
      simp_rw [heval, Homeomorph.apply_symm_apply]
    _ = (∫ q, g q ∂νZ) * ∫ w, unitTail w ∂ρ := integral_prod_mul _ _
    _ = _ := by rw [hmass, mul_one]

end Measures

/-- The unit orbital-integral comparison in product coordinates. -/
def CyclicProductUnitOrbitalReductionStatement : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (m : ℕ) (κ : H ≃ₜ* (Fin (m + 1) → G)) (σ : H →* H) (τ : G →* G)
    (hshift : ∀ (x : H) (i : Fin m), κ (σ x) i.castSucc = κ x i.succ)
    (hwrap : ∀ x : H, κ (σ x) (Fin.last m) = τ (κ x 0)) (δ : H),
    Continuous σ → Continuous τ →
    let y := (List.ofFn (κ δ)).prod
    let C := twistedCentralizer σ δ
    let Z := twistedCentralizer τ y
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (μH : Measure H),
      MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) ↦ μ) →
      ∀ (μC : Measure C) [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
        (μZ : Measure Z) [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
        (νC : Measure (LeftQuotient C)) (νZ : Measure (LeftQuotient Z)),
        IsCompatible C μH μC νC → IsCompatible Z μ μZ νZ →
        MeasurePreserving (cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ) μC μZ →
        ∀ (K : Subgroup G), MeasurableSet (K : Set G) → μ K = 1 →
          twistedOrbitalIntegral σ δ νC (fun x ↦ (Set.pi Set.univ
            (fun _ : Fin (m + 1) ↦ (K : Set G))).indicator (fun _ ↦ 1) (κ x)) =
          twistedOrbitalIntegral τ y νZ ((K : Set G).indicator (fun _ ↦ 1))

theorem cyclicProductUnitOrbitalReduction : CyclicProductUnitOrbitalReductionStatement := by
  intro H _ _ _ _ _ G _ _ _ _ _ _ _ _ m κ σ τ hshift hwrap δ hσ hτ
  dsimp only
  intro μ _ μH hκ μC _ _ μZ _ _ νC νZ hνC hνZ he K hK hvol
  exact cyclicProductUnitOrbitalIntegral_eq κ σ τ hshift hwrap δ
    hσ hτ hκ hνC hνZ he K hK hvol

end Langlands.BaseChange
