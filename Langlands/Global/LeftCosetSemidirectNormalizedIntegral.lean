import Langlands.Global.AdelicSubgroupHaarNormalization
import Langlands.Global.LeftCosetSemidirectPeriod

/-! # Normalized Haar and integration along split discrete quotients -/

noncomputable section

universe u

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace.Semidirect

private theorem out_eval_mk {X : Type u} [Group X] (Λ : Subgroup X) (f : X → ℂ)
    (hf : ∀ a : Λ, ∀ x, f (a.val * x) = f x) (x : X) :
    f (Quotient.out (mk Λ x)) = f x := by
  let f' := lift Λ f hf
  exact congrArg f' (Quotient.out_eq (mk Λ x))

private theorem continuous_out_eval {X : Type u} [Group X] [TopologicalSpace X]
    (Λ : Subgroup X) (f : X → ℂ) (hf : ∀ a : Λ, ∀ x, f (a.val * x) = f x)
    (hc : Continuous f) : Continuous (fun z : LeftCosetSpace Λ => f z.out) := by
  apply (continuous_iff Λ).mpr
  change Continuous (fun x => f (Quotient.out (mk Λ x)))
  simpa only [out_eval_mk Λ f hf] using hc

variable {N M H : Type u} [Group N] [Group M] [Group H]
  [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H]
  [IsTopologicalGroup N] [IsTopologicalGroup M] [IsTopologicalGroup H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [LocallyCompactSpace N] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m)
  (hker : ∀ h, p h = 1 → ∃ n, i n = h)
  (hpi : ∀ n, p (i n) = 1)
  (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)

/-- Haar scaled by the inverse mass of the chosen lattice domain. -/
def latticeNormalizedHaar {X : Type u} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Γ : Subgroup X) (hΓ : IsDiscrete (Γ : Set X)) :
    Measure X :=
  ((Measure.haar : Measure X) (fundamentalDomain Γ hΓ))⁻¹ • Measure.haar

local notation "Φ" => prodHomeomorph i j p hpj hker hpi hi hj hp

variable (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ΓM : Subgroup M) (hΓM : IsDiscrete (ΓM : Set M))
  (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N))

/-- Normalizing three Haar measures by the full split lattice makes the
semidirect product coordinates exactly measure preserving. -/
def SemidirectNormalizedHaarStatement : Prop :=
  (∀ m ∈ ΓM, j m ∈ Γ) → (∀ h ∈ Γ, p h ∈ ΓM) →
  IsFiniteMeasure (haarQuotientMeasure (Γ.comap i) hΓN) →
  IsFiniteMeasure (haarQuotientMeasure ΓM hΓM) →
  latticeNormalizedHaar Γ hΓ =
    ((latticeNormalizedHaar (Γ.comap i) hΓN).prod (latticeNormalizedHaar ΓM hΓM)).map Φ

set_option maxHeartbeats 1400000 in
theorem semidirectNormalizedHaar :
    SemidirectNormalizedHaarStatement i j p hpj hker hpi hi hj hp Γ hΓ ΓM hΓM hΓN := by
  intro hjΓ hpΓ hfinN hfinM
  let : IsFiniteMeasure (haarQuotientMeasure (Γ.comap i) hΓN) := hfinN
  let : IsFiniteMeasure (haarQuotientMeasure ΓM hΓM) := hfinM
  let DN := fundamentalDomain (Γ.comap i) hΓN
  let DM := fundamentalDomain ΓM hΓM
  let E := DN ×ˢ DM
  let e := Φ
  let ν := (Measure.haar : Measure N).prod (Measure.haar : Measure M)
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  have hDom := isFundamentalDomain_product i j p hpj hker hpi hi hj hp Γ ΓM hΓM hjΓ hpΓ hΓN
  have hMass : (Measure.haar : Measure H) (fundamentalDomain Γ hΓ) = Measure.haar (Φ '' E) :=
    (isFundamentalDomain Γ hΓ Measure.haar).measure_eq hDom
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp
    (mulEquivHaarChar_conj_eq_one_of_finiteCovolume
      i j p hpj hker hpi hi hj Γ ΓM hΓM hjΓ hΓN)
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    have hc' : (Measure.haar : Measure H) = (c : ℝ≥0∞) • ν.map Φ := hc
    rw [h, zero_smul] at hc'
    exact (NeZero.ne _) hc'
  have hc' : (Measure.haar : Measure H) = (c : ℝ≥0∞) • ν.map Φ := hc
  have hMapMass : (ν.map Φ) (Φ '' E) = ν E := by
    change (ν.map e) (e '' E) = _
    have hE : MeasurableSet (Φ '' E) := by
      change MeasurableSet (e '' E)
      rw [e.image_eq_preimage_symm]
      exact e.symm.continuous.measurable ((measurableSet_fundamentalDomain (Γ.comap i) hΓN).prod
        (measurableSet_fundamentalDomain ΓM hΓM))
    rw [Measure.map_apply e.continuous.measurable hE, e.preimage_image]
  unfold latticeNormalizedHaar
  rw [hMass, hc', normalizedAmbientMeasure_smul _ _ _ hc0 ENNReal.coe_ne_top, hMapMass]
  have hn0 : (Measure.haar : Measure N) DN ≠ 0 := haar_fundamentalDomain_ne_zero _ _
  have hnTop : (Measure.haar : Measure N) DN ≠ ∞ := haar_fundamentalDomain_ne_top _ _
  change (ν E)⁻¹ • (ν.map Φ) = _
  rw [show ν E = (Measure.haar : Measure N) DN * (Measure.haar : Measure M) DM from
      Measure.prod_prod _ _,
    ENNReal.mul_inv (Or.inl hn0) (Or.inl hnTop),
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  exact e.continuous.measurable.aemeasurable

section Fubini

variable (Δ : Subgroup H) (hΔ : IsDiscrete (Δ : Set H))
  (hΔN : IsDiscrete ((Δ.comap i : Subgroup N) : Set N))
  (hjΔ : ∀ m ∈ ΓM, j m ∈ Δ) (hpΔ : ∀ h ∈ Δ, p h ∈ ΓM)
  (μN : Measure N) (μM : Measure M) (μH : Measure H)
  [μN.IsHaarMeasure] [μM.IsHaarMeasure] [μH.IsHaarMeasure]

omit [LocallyCompactSpace H] in
include hjΔ hpΔ in
/-- The lattice in the normal factor may be replaced by a discrete
subgroup while keeping the original Haar normalizations. -/
theorem integral_fundamentalDomain_split
    (hμ : μH = (μN.prod μM).map Φ)
    (f : H → ℂ) (hInv : ∀ γ : Δ, ∀ x, f (γ.val * x) = f x)
    (hf : IntegrableOn f (fundamentalDomain Δ hΔ) μH) :
    ∫ x in fundamentalDomain Δ hΔ, f x ∂μH =
      ∫ m in fundamentalDomain ΓM hΓM,
        ∫ n in fundamentalDomain (Δ.comap i) hΔN, f (i n * j m) ∂μN ∂μM := by
  let E := fundamentalDomain (Δ.comap i) hΔN ×ˢ fundamentalDomain ΓM hΓM
  let e := Φ
  have hE : MeasurableSet E :=
    (measurableSet_fundamentalDomain (Δ.comap i) hΔN).prod (measurableSet_fundamentalDomain ΓM hΓM)
  have hImg : MeasurableSet (e '' E) := by
    rw [e.image_eq_preimage_symm]
    exact e.symm.continuous.measurable hE
  have hDom : IsFundamentalDomain Δ (e '' E) μH :=
    IsFundamentalDomain.mk' hImg.nullMeasurableSet
      (productFundamentalDomain_unique i j p hpj hker hpi hi hj hp Δ ΓM hΓM hjΔ hpΔ hΔN)
  let : Countable Δ := countable_of_isDiscrete Δ hΔ
  have hOriginal := isFundamentalDomain Δ hΔ μH
  rw [hOriginal.setIntegral_eq hDom hInv, hμ, e.isClosedEmbedding.setIntegral_map, e.preimage_image]
  have hI : IntegrableOn f (e '' E) μH := (hOriginal.integrableOn_iff hDom hInv).mp hf
  rw [hμ] at hI
  let ν := μN.prod μM
  have hmp : MeasurePreserving e (ν.restrict E) ((ν.map e).restrict (e '' E)) := by
    simpa only [e.preimage_image] using
      (show MeasurePreserving e ν (ν.map e) from ⟨e.continuous.measurable, rfl⟩).restrict_preimage hImg
  have hpI := hmp.integrable_comp_of_integrable hI
  change Integrable (f ∘ Φ)
    ((μN.prod μM).restrict (fundamentalDomain (Δ.comap i) hΔN ×ˢ fundamentalDomain ΓM hΓM)) at hpI
  rw [← Measure.prod_restrict] at hpI
  change (∫ x in fundamentalDomain (Δ.comap i) hΔN ×ˢ fundamentalDomain ΓM hΓM,
      (f ∘ Φ) x ∂μN.prod μM) = _
  rw [← Measure.prod_restrict, integral_prod_symm _ hpI]
  rfl

omit [LocallyCompactSpace H] in
include hjΔ hpΔ in
/-- The same equality expressed on the defining quotient measures and the
chosen representatives. The outer average descends as a continuous function. -/
theorem integral_discreteQuotient_split
    [BorelSpace (LeftCosetSpace Δ)] [BorelSpace (LeftCosetSpace (Δ.comap i))]
    [BorelSpace (LeftCosetSpace ΓM)]
    (hμ : μH = (μN.prod μM).map Φ)
    (f : H → ℂ) (hfc : Continuous f) (hInv : ∀ γ : Δ, ∀ x, f (γ.val * x) = f x)
    (hf : Integrable (fun z : LeftCosetSpace Δ => f z.out) (discreteQuotientMeasure Δ hΔ μH))
    (A : M → ℂ) (hAc : Continuous A) (hAinv : ∀ γ : ΓM, ∀ x, A (γ.val * x) = A x)
    (hA : ∀ m, A m = ∫ z : LeftCosetSpace (Δ.comap i), f (i z.out * j m)
      ∂discreteQuotientMeasure (Δ.comap i) hΔN μN) :
    ∫ z : LeftCosetSpace Δ, f z.out ∂discreteQuotientMeasure Δ hΔ μH =
      ∫ z : LeftCosetSpace ΓM, A z.out ∂discreteQuotientMeasure ΓM hΓM μM := by
  have hF : IntegrableOn f (fundamentalDomain Δ hΔ) μH := by
    have h := (integrable_quotientMeasure_iff Δ μH (fundamentalDomain Δ hΔ)
      (fun z => f z.out) hf.aestronglyMeasurable).mp hf
    simpa only [out_eval_mk Δ f hInv] using h
  have hInner (m : M) : A m =
      ∫ n in fundamentalDomain (Δ.comap i) hΔN, f (i n * j m) ∂μN := by
    let k := fun n : N => f (i n * j m)
    have hInvN (a : Δ.comap i) (x : N) : k (a.val * x) = k x := by
      unfold k
      rw [map_mul, mul_assoc]
      exact hInv ⟨i a.val, a.property⟩ (i x * j m)
    have hkc : Continuous k := hfc.comp (hi.continuous.mul_const _)
    rw [hA]
    change (∫ z : LeftCosetSpace (Δ.comap i), k z.out
      ∂quotientMeasure (Δ.comap i) μN (fundamentalDomain (Δ.comap i) hΔN)) = _
    rw [integral_quotientMeasure _ _ _ _
      (continuous_out_eval (Δ.comap i) k hInvN hkc).aestronglyMeasurable]
    simp only [out_eval_mk (Δ.comap i) k hInvN, k]
  have hL := integral_quotientMeasure Δ μH (fundamentalDomain Δ hΔ) (fun z => f z.out)
    (continuous_out_eval Δ f hInv hfc).aestronglyMeasurable
  have hR := integral_quotientMeasure ΓM μM (fundamentalDomain ΓM hΓM) (fun z => A z.out)
    (continuous_out_eval ΓM A hAinv hAc).aestronglyMeasurable
  rw [discreteQuotientMeasure, discreteQuotientMeasure, hL, hR]
  simp only [out_eval_mk Δ f hInv, out_eval_mk ΓM A hAinv, hInner]
  exact integral_fundamentalDomain_split i j p hpj hker hpi hi hj hp ΓM hΓM Δ hΔ hΔN
    hjΔ hpΔ μN μM μH hμ f hInv hF

end Fubini

end Langlands.Global.LeftCosetSpace.Semidirect
