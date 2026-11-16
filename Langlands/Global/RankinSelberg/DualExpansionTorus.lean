import Langlands.Automorphic.CuspidalWhittaker.QuotientTorus
import Langlands.Global.RankinSelberg.DualExpansionSums

/-! # Torus integrals: characters, empty and split index types, and sums -/

noncomputable section
universe u
open MeasureTheory NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable {F : Type u} [Field F] [NumberField F]

section Character

variable {ι : Type*} [Fintype ι]

/-- The pairing character `y ↦ ψ(Σ a_i y_i)` attached to a rational vector `a`. -/
def pairChar (ψ : AddChar (Adeles F) ℂ) (a : ι → F) (y : ι → Adeles F) : ℂ :=
  ψ (∑ i, algebraMap F (Adeles F) (a i) * y i)

theorem pairChar_add (ψ : AddChar (Adeles F) ℂ) (a : ι → F) (y z : ι → Adeles F) :
    pairChar ψ a (y + z) = pairChar ψ a y * pairChar ψ a z := by
  simp only [pairChar, Pi.add_apply, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

theorem isPeriodic_pairChar (ψ : AddChar (Adeles F) ℂ)
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (a : ι → F) :
    IsPeriodic (pairChar ψ a) := by
  intro y k
  rw [pairChar_add]
  have : pairChar ψ a (ratVec k) = 1 := by
    simp only [pairChar, ratVec_apply, ← map_mul, ← map_sum, hψF]
  rw [this, mul_one]

theorem continuous_pairChar (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ) (a : ι → F) :
    Continuous (pairChar ψ a) := by
  unfold pairChar
  exact hψ.comp (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))

variable [CompactSpace (AdeleQuotient F)]

open Classical in
/-- Orthogonality of the pairing characters on `(𝔸/F)^ι`. -/
theorem torusIntegral_pairChar [DecidableEq ι] (ψ : AddChar (Adeles F) ℂ)
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (hψn : ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1)
    (a : ι → F) :
    torusIntegral ι (pairChar ψ a) = if a = 0 then 1 else 0 := by
  split_ifs with ha
  · subst ha
    have : pairChar ψ (0 : ι → F) = fun _ => 1 := by
      funext y
      simp [pairChar]
    rw [this, torusIntegral_const]
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha
    obtain ⟨y₀, hy₀⟩ := hψn (a i₀) hi₀
    have h := torusIntegral_add_right (isPeriodic_pairChar ψ hψF a) (Pi.single i₀ y₀)
    simp_rw [pairChar_add] at h
    rw [torusIntegral_mul_const] at h
    have hz : pairChar ψ a (Pi.single i₀ y₀) = ψ (algebraMap F (Adeles F) (a i₀) * y₀) := by
      simp only [pairChar, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [hz] at h
    have h2 : torusIntegral ι (pairChar ψ a) * (ψ (algebraMap F (Adeles F) (a i₀) * y₀) - 1) =
        0 := by
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hy₀

end Character

variable [CompactSpace (AdeleQuotient F)]

section Index

variable {ι : Type*} [Fintype ι]

/-- A torus integral over an empty index type is evaluation at `0`. -/
theorem torusIntegral_of_isEmpty [IsEmpty ι] (f : (ι → Adeles F) → ℂ) :
    torusIntegral ι f = f 0 := by
  unfold torusIntegral
  have : ∀ t : ι → AdeleQuotient F, torusLift t = (0 : ι → Adeles F) :=
    fun t => Subsingleton.elim _ _
  simp only [this, integral_const, probReal_univ, one_smul]

/-- Fubini over a sum of index types. -/
theorem torusIntegral_sum_elim {α β : Type*} [Fintype α] [Fintype β]
    {g : (α ⊕ β → Adeles F) → ℂ} (hg : IsPeriodic g) (hc : Continuous g) :
    torusIntegral (α ⊕ β) g =
      torusIntegral α (fun x => torusIntegral β (fun y => g (Sum.elim x y))) := by
  unfold torusIntegral
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : α ⊕ β => AdeleQuotient F) (fun _ => adeleQuotientHaar F)
  change ∫ t, g (torusLift t) ∂(Measure.pi fun _ => adeleQuotientHaar F) = _
  rw [← hmp.integral_comp' (fun t => g (torusLift t))]
  have hsym : Continuous fun p : (α → AdeleQuotient F) × (β → AdeleQuotient F) =>
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => AdeleQuotient F)).symm p := by
    refine continuous_pi fun i => ?_
    cases i with
    | inl a => exact (continuous_apply a).comp continuous_fst
    | inr b => exact (continuous_apply b).comp continuous_snd
  have hcont : Continuous fun p : (α → AdeleQuotient F) × (β → AdeleQuotient F) =>
      g (torusLift ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : α ⊕ β => AdeleQuotient F)).symm p)) :=
    (hg.continuous_lift hc).comp hsym
  rw [integral_prod _ (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  refine integral_congr_ae (ae_of_all _ fun s => integral_congr_ae (ae_of_all _ fun t => ?_))
  apply hg.eq_of_torusMk_eq
  rw [torusMk_torusLift]
  funext i
  cases i with
  | inl a => exact (congrFun (torusMk_torusLift s) a).symm
  | inr b => exact (congrFun (torusMk_torusLift t) b).symm

/-- Reindexing a torus integral along an equivalence of index types. -/
def reindexHom {ι κ : Type*} (e : ι ≃ κ) : (ι → Adeles F) →+ (κ → Adeles F) where
  toFun y k := y (e.symm k)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem torusIntegral_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    {f : (κ → Adeles F) → ℂ} (hf : IsPeriodic f) (hc : Continuous f) :
    torusIntegral ι (fun y => f (fun k => y (e.symm k))) = torusIntegral κ f :=
  torusIntegral_comp hf hc (φ := reindexHom e) (fun k => ⟨fun j => k (e.symm j), rfl⟩)
    (continuous_pi fun k => continuous_apply _)
    (fun z => ⟨fun i => z (e i), by funext k; simp [reindexHom]⟩)

theorem norm_torusIntegral_le {ι : Type*} [Fintype ι] {f : (ι → Adeles F) → ℂ} {B : ℝ}
    (hB : ∀ y, ‖f y‖ ≤ B) : ‖torusIntegral ι f‖ ≤ B := by
  unfold torusIntegral
  have := norm_integral_le_of_norm_le_const (μ := torusHaar F ι) (C := B)
    (Filter.Eventually.of_forall fun t => hB (torusLift t))
  simpa using this

/-- Exchanging a torus integral with an absolutely and boundedly convergent sum of continuous
periodic functions. -/
theorem torusIntegral_tsum {ι Q : Type*} [Fintype ι] [Countable Q]
    {f : Q → (ι → Adeles F) → ℂ} (hc : ∀ q, Continuous (f q)) (hp : ∀ q, IsPeriodic (f q))
    (hs : ∀ y, Summable fun q => ‖f q y‖) {B : ℝ} (hB : ∀ y, ∑' q, ‖f q y‖ ≤ B) :
    torusIntegral ι (fun y => ∑' q, f q y) = ∑' q, torusIntegral ι (f q) := by
  unfold torusIntegral
  have hm : ∀ q, Continuous fun t => f q (torusLift t) := fun q => (hp q).continuous_lift (hc q)
  refine integral_tsum (fun q => (hm q).aestronglyMeasurable) ?_
  rw [← lintegral_tsum (fun q => (hm q).enorm.aemeasurable)]
  refine ne_top_of_le_ne_top (b := ∫⁻ _ : ι → AdeleQuotient F, ENNReal.ofReal B ∂torusHaar F ι)
    (by simp) (lintegral_mono fun t => ?_)
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg _) (hs _)]
  exact ENNReal.ofReal_le_ofReal (hB _)

/-- Sums of absolute values of torus integrals are bounded by uniform bounds on the sums of
absolute values of the integrands. -/
theorem sum_norm_torusIntegral_le {ι Q : Type*} [Fintype ι] {G : Q → (ι → Adeles F) → ℂ}
    (hc : ∀ q, Continuous (G q)) (hp : ∀ q, IsPeriodic (G q))
    (hs : ∀ y, Summable fun q => ‖G q y‖) {B : ℝ} (hB : ∀ y, ∑' q, ‖G q y‖ ≤ B)
    (s : Finset Q) :
    ∑ q ∈ s, ‖torusIntegral ι (G q)‖ ≤ B := by
  classical
  set ε : Q → ℂ := fun q => if torusIntegral ι (G q) = 0 then 0 else
    (starRingEnd ℂ (torusIntegral ι (G q))) / ‖torusIntegral ι (G q)‖
  have hε : ∀ q, ε q * torusIntegral ι (G q) = ‖torusIntegral ι (G q)‖ := by
    intro q
    simp only [ε]
    split_ifs with h
    · rw [h]; simp
    · rw [div_mul_eq_mul_div, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_pow]
      field_simp [norm_ne_zero_iff.mpr h]
  have hεn : ∀ q, ‖ε q‖ ≤ 1 := by
    intro q
    simp only [ε]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]
  have hlin : ∑ q ∈ s, ε q * torusIntegral ι (G q) =
      torusIntegral ι (fun y => ∑ q ∈ s, ε q * G q y) := by
    unfold torusIntegral
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_const_mul]
    · intro q _
      exact ((hp q).continuous_lift (hc q)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) |>.const_mul _
  have hreal : (∑ q ∈ s, ‖torusIntegral ι (G q)‖ : ℝ) =
      ‖torusIntegral ι (fun y => ∑ q ∈ s, ε q * G q y)‖ := by
    rw [← hlin]
    simp_rw [hε]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  rw [hreal]
  refine norm_torusIntegral_le fun y => ?_
  calc ‖∑ q ∈ s, ε q * G q y‖ ≤ ∑ q ∈ s, ‖G q y‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hεn q)
    _ ≤ ∑' q, ‖G q y‖ := (hs y).sum_le_tsum s fun _ _ => norm_nonneg _
    _ ≤ B := hB y

end Index

end Langlands.Global.RankinSelbergGlobal.Unfolding
