import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Weighted integration along the factors of a finite product -/

noncomputable section

open MeasureTheory Set

namespace Langlands.Archimedean.RealCartanProductAverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [FirstCountableTopology G] [LocallyCompactSpace G]

section Single

variable {H : Type*} [TopologicalSpace H] [T2Space H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

omit [FirstCountableTopology G] [LocallyCompactSpace G] [T2Space H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H] in
private theorem continuous_weightedIntegrand (r : C(H, G)) (w : C(H, ℂ)) (f : C(G, ℂ)) :
    Continuous fun p : G × H => w p.2 * f (r p.2 * p.1) :=
  (w.continuous.comp continuous_snd).mul
    (f.continuous.comp ((r.continuous.comp continuous_snd).mul continuous_fst))

/-- Integrate left translates against a continuous weight on a compact space. -/
def weightedAverage (μ : Measure H) [IsFiniteMeasure μ] (r : C(H, G))
    (w : C(H, ℂ)) : Module.End ℂ C(G, ℂ) where
  toFun f := ⟨fun x => ∫ h, w h * f (r h * x) ∂μ, by
    have hc := continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun x h => w h * f (r h * x)) (continuous_weightedIntegrand r w f) (isCompact_univ (X := H))
    simpa only [Measure.restrict_univ] using hc⟩
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    change (∫ h, w h * (f (r h * x) + g (r h * x)) ∂μ) =
      (∫ h, w h * f (r h * x) ∂μ) + (∫ h, w h * g (r h * x) ∂μ)
    simp_rw [mul_add]
    have hint (F : C(G, ℂ)) : Integrable (fun h => w h * F (r h * x)) μ :=
      ((continuous_weightedIntegrand r w F).comp
        (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact integral_add (hint f) (hint g)
  map_smul' a f := by
    apply ContinuousMap.ext
    intro x
    change (∫ h, w h * (a * f (r h * x)) ∂μ) = a * ∫ h, w h * f (r h * x) ∂μ
    rw [← integral_const_mul]
    congr 1
    funext h
    ring

set_option linter.unusedSectionVars false in
@[simp]
theorem weightedAverage_apply (μ : Measure H) [IsFiniteMeasure μ] (r : C(H, G))
    (w : C(H, ℂ)) (f : C(G, ℂ)) (x : G) :
    weightedAverage μ r w f x = ∫ h, w h * f (r h * x) ∂μ := rfl

end Single

section Product

variable {c : ℕ} {H : Fin c → Type*} [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]

private theorem continuous_mulSingle (i : Fin c) :
    Continuous (Pi.mulSingle (M := H) i) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same]
    exact continuous_id
  · simpa only [Pi.mulSingle_eq_of_ne h] using (continuous_const : Continuous fun _ : H i => (1 : H j))

variable [∀ i, T2Space (H i)] [∀ i, CompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]
  [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

/-- The weighted average in one factor, using the corresponding product embedding. -/
def factorAverage (ρ : (∀ i, H i) →* G) (hρ : Continuous ρ)
    (μ : ∀ i, Measure (H i)) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ∀ i, C(H i, ℂ)) (i : Fin c) : Module.End ℂ C(G, ℂ) :=
  weightedAverage (μ i) ⟨fun a => ρ (Pi.mulSingle i a), hρ.comp (continuous_mulSingle i)⟩ (w i)

set_option linter.unusedSectionVars false in
@[simp]
theorem factorAverage_apply (ρ : (∀ i, H i) →* G) (hρ : Continuous ρ)
    (μ : ∀ i, Measure (H i)) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ∀ i, C(H i, ℂ)) (i : Fin c) (f : C(G, ℂ)) (x : G) :
    factorAverage ρ hρ μ w i f x = ∫ a, w i a * f (ρ (Pi.mulSingle i a) * x) ∂μ i := rfl

end Product

section Tail

variable {c : ℕ} {H : Fin (c + 1) → Type*} [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]

private def tailInclusion : ((i : Fin c) → H i.succ) →* (∀ i, H i) where
  toFun v := Fin.cons 1 v
  map_one' := by
    funext i
    cases i using Fin.cases <;> simp
  map_mul' u v := by
    funext i
    cases i using Fin.cases <;> simp

private theorem continuous_tailInclusion : Continuous (tailInclusion (H := H)) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases
  · exact continuous_const
  · exact continuous_apply _

omit [∀ i, TopologicalSpace (H i)] in
private theorem tailInclusion_mulSingle (i : Fin c) (a : H i.succ) :
    tailInclusion (Pi.mulSingle i a) = Pi.mulSingle i.succ a := by
  funext j
  cases j using Fin.cases with
  | zero => simp [tailInclusion]
  | succ j =>
    by_cases h : j = i
    · subst j
      simp [tailInclusion]
    · simp [tailInclusion, Pi.mulSingle_eq_of_ne h, Fin.succ_inj.ne.mpr h]

omit [∀ i, TopologicalSpace (H i)] in
private theorem tailInclusion_mul_first (a : H 0) (v : (i : Fin c) → H i.succ) :
    tailInclusion v * Pi.mulSingle 0 a = Fin.cons a v := by
  funext i
  cases i using Fin.cases <;> simp [tailInclusion]

end Tail

/-- Composing the finite list of factor averages gives the product-measure average. -/
def RealCartanProductAverageStatement (G : Type*) [Monoid G] [TopologicalSpace G]
    [ContinuousMul G] [FirstCountableTopology G] [LocallyCompactSpace G] : Prop :=
  ∀ (c : ℕ) (H : Fin c → Type*) [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, T2Space (H i)] [∀ i, CompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (ρ : (∀ i, H i) →* G) (hρ : Continuous ρ)
    (μ : ∀ i, Measure (H i)) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ∀ i, C(H i, ℂ)) (f : C(G, ℂ)) (x : G),
    ((List.finRange c).map (factorAverage ρ hρ μ w)).prod f x =
      ∫ a, (∏ i, w i (a i)) * f (ρ a * x) ∂Measure.pi μ

set_option maxHeartbeats 700000 in
theorem realCartanProductAverage : RealCartanProductAverageStatement G := by
  intro c
  induction c with
  | zero =>
    intro H _ _ _ _ _ _ _ ρ _ μ _ w f x
    simp only [List.finRange_zero, List.map_nil, List.prod_nil, Module.End.one_apply,
      Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    have he (a : ∀ i, H i) : a = 1 := funext fun i => i.elim0
    simp only [he, map_one, one_mul, integral_const, probReal_univ, one_smul]
  | succ c ih =>
    intro H _ _ _ _ _ _ _ ρ hρ μ _ w f x
    let ρ' : ((i : Fin c) → H i.succ) →* G := ρ.comp tailInclusion
    have hρ' : Continuous ρ' := hρ.comp continuous_tailInclusion
    have hfactor (i : Fin c) : factorAverage ρ hρ μ w i.succ =
        factorAverage ρ' hρ' (fun i => μ i.succ) (fun j => w j.succ) i := by
      apply LinearMap.ext
      intro F
      apply ContinuousMap.ext
      intro y
      simp only [factorAverage_apply, ρ', MonoidHom.comp_apply, tailInclusion_mulSingle]
    rw [List.finRange_succ, List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_map]
    have htail : (List.finRange c).map (fun i => factorAverage ρ hρ μ w i.succ) =
        (List.finRange c).map (factorAverage ρ' hρ' (fun i => μ i.succ) (fun j => w j.succ)) := by
      rw [show (fun i : Fin c => factorAverage ρ hρ μ w i.succ) = _ from funext hfactor]
    change factorAverage ρ hρ μ w 0 (((List.finRange c).map
      (fun i => factorAverage ρ hρ μ w i.succ)).prod f) x = _
    rw [htail, factorAverage_apply]
    simp_rw [ih _ ρ' hρ']
    have hmul (a : H 0) (v : (i : Fin c) → H i.succ) :
        ρ' v * (ρ (Pi.mulSingle 0 a) * x) = ρ (Fin.cons a v) * x := by
      change ρ (tailInclusion v) * (ρ (Pi.mulSingle 0 a) * x) = _
      rw [← mul_assoc, ← map_mul, tailInclusion_mul_first]
    simp_rw [hmul, ← integral_const_mul, ← mul_assoc]
    let I (v : ∀ i, H i) := (∏ i, w i (v i)) * f (ρ v * x)
    have hI : Continuous I := (continuous_finsetProd _ fun i _ =>
      (w i).continuous.comp (continuous_apply i)).mul (f.continuous.comp (hρ.mul continuous_const))
    let e := MeasurableEquiv.piFinSuccAbove H (0 : Fin (c + 1))
    have hm := (measurePreserving_piFinSuccAbove μ (0 : Fin (c + 1))).symm
    have hcoe (p : H 0 × ((i : Fin c) → H i.succ)) : e.symm p = Fin.cons p.1 p.2 := by
      funext i
      cases i using Fin.cases <;> simp [e, MeasurableEquiv.piFinSuccAbove]
    let J (p : H 0 × ((i : Fin c) → H i.succ)) := I (Fin.cons p.1 p.2)
    have hc : Continuous J := hI.comp (by
      apply continuous_pi
      intro i
      cases i using Fin.cases with
      | zero => exact continuous_fst
      | succ i =>
        change Continuous (fun p : H 0 × ((j : Fin c) → H j.succ) => p.2 i)
        exact (continuous_apply i).comp continuous_snd)
    have hInt := hc.integrable_of_hasCompactSupport (μ := (μ 0).prod
      (Measure.pi fun i : Fin c => μ i.succ)) (HasCompactSupport.of_compactSpace _)
    change (∫ a, ∫ v, w 0 a * (∏ i : Fin c, w i.succ (v i)) * f (ρ (Fin.cons a v) * x)
      ∂Measure.pi (fun i => μ i.succ) ∂μ 0) = ∫ v, I v ∂Measure.pi μ
    calc
      _ = ∫ p, J p ∂(μ 0).prod (Measure.pi fun i : Fin c => μ i.succ) := by
        rw [integral_prod _ hInt]
        simp only [J, I, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      _ = _ := by
        have hJ (p : H 0 × ((i : Fin c) → H i.succ)) : J p = I (e.symm p) :=
          congrArg I (hcoe p).symm
        simp_rw [hJ]
        exact hm.integral_comp' I

end Langlands.Archimedean.RealCartanProductAverage
