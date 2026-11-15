import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Fourier series for an orthonormal family of characters on a compact space

Let `X` be a compact Hausdorff space with a Borel probability measure `ν` of full support, and
let `e : ι → C(X, ℂ)`, indexed by an additive group, be a family of unimodular functions with
`e 0 = 1`, `e (i + j) = e i * e j`, `e (-i) = conj (e i)`, which separates the points of `X`
and satisfies `∫ e i dν = 0` for `i ≠ 0`. Then a continuous function with vanishing Fourier
coefficients is zero, and a continuous function with absolutely summable Fourier coefficients
is the pointwise sum of its Fourier series.
-/

noncomputable section
open MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- A family of unimodular continuous functions closed under products and conjugation. -/
structure IsCharacterFamily {ι : Type*} [AddGroup ι] (e : ι → C(X, ℂ)) : Prop where
  zero : e 0 = 1
  add : ∀ i j, e (i + j) = e i * e j
  neg : ∀ i, e (-i) = star (e i)
  norm_apply : ∀ i x, ‖e i x‖ = 1

/-- The Fourier coefficient `∫ f · conj (e i) dν`. -/
def fourierCoeff (ν : Measure X) {ι : Type*} (e : ι → C(X, ℂ)) (f : C(X, ℂ)) (i : ι) : ℂ :=
  ∫ x, f x * star (e i x) ∂ν

section Pairing

variable (ν : Measure X) [IsFiniteMeasure ν]

omit [T2Space X] in
theorem integrable_continuousMap {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (f : C(X, E)) :
    Integrable f ν :=
  (BoundedContinuousFunction.mkOfCompact f).integrable ν

/-- The continuous linear functional `p ↦ ∫ p · g dν` on `C(X, ℂ)`. -/
def pairingCLM (g : C(X, ℂ)) : C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun p => ∫ x, p x * g x ∂ν
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_continuousMap ν (p * g))
          (integrable_continuousMap ν (q * g))
      map_smul' := fun a p => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul a _ }
    (ν.real Set.univ * ‖g‖) (fun p => by
      change ‖∫ x, p x * g x ∂ν‖ ≤ _
      calc ‖∫ x, p x * g x ∂ν‖ ≤ ‖p‖ * ‖g‖ * ν.real Set.univ := by
            apply norm_integral_le_of_norm_le_const
            refine Filter.Eventually.of_forall fun x => ?_
            rw [norm_mul]
            exact mul_le_mul (p.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _)
              (norm_nonneg _)
        _ = ν.real Set.univ * ‖g‖ * ‖p‖ := by ring)

omit [T2Space X] in
theorem pairingCLM_apply (g p : C(X, ℂ)) : pairingCLM ν g p = ∫ x, p x * g x ∂ν := rfl

end Pairing

section Algebra

variable {ι : Type*} [AddGroup ι] {e : ι → C(X, ℂ)}

/-- The span of the family is a star subalgebra. -/
def characterAlgebra (he : IsCharacterFamily e) : StarSubalgebra ℂ C(X, ℂ) where
  carrier := Submodule.span ℂ (Set.range e)
  mul_mem' := by
    intro p q hp hq
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      induction hq using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨j, rfl⟩ := hq
        rw [← he.add]
        exact Submodule.subset_span ⟨i + j, rfl⟩
      | zero => simp
      | add q r _ _ hq hr => rw [mul_add]; exact Submodule.add_mem _ hq hr
      | smul a q _ hq => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hq
    | zero => simp
    | add p r _ _ hp hr => rw [add_mul]; exact Submodule.add_mem _ hp hr
    | smul a p _ hp => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hp
  one_mem' := by
    rw [← he.zero]
    exact Submodule.subset_span ⟨0, rfl⟩
  add_mem' := fun hp hq => Submodule.add_mem _ hp hq
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    rw [← he.zero]
    exact Submodule.subset_span ⟨0, rfl⟩
  star_mem' := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      rw [← he.neg]
      exact Submodule.subset_span ⟨-i, rfl⟩
    | zero => simp
    | add p q _ _ hp hq => rw [star_add]; exact Submodule.add_mem _ hp hq
    | smul a p _ hp => rw [star_smul]; exact Submodule.smul_mem _ _ hp

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem characterAlgebra_coe (he : IsCharacterFamily e) :
    ((characterAlgebra he : StarSubalgebra ℂ C(X, ℂ)) : Set C(X, ℂ)) =
      Submodule.span ℂ (Set.range e) := rfl

omit [MeasurableSpace X] [BorelSpace X] in
theorem characterAlgebra_topologicalClosure (he : IsCharacterFamily e)
    (hsep : ∀ x y : X, x ≠ y → ∃ i, e i x ≠ e i y) :
    (characterAlgebra he).topologicalClosure = ⊤ := by
  apply ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
  intro x y hxy
  obtain ⟨i, hi⟩ := hsep x y hxy
  exact ⟨e i, ⟨e i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩, hi⟩

end Algebra

variable (ν : Measure X) [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
variable {ι : Type*} [AddGroup ι] {e : ι → C(X, ℂ)}

/-- A continuous function all of whose Fourier coefficients vanish is zero. -/
theorem eq_zero_of_fourierCoeff_eq_zero (he : IsCharacterFamily e)
    (hsep : ∀ x y : X, x ≠ y → ∃ i, e i x ≠ e i y) (f : C(X, ℂ))
    (hf : ∀ i, fourierCoeff ν e f i = 0) : f = 0 := by
  have hker : (Submodule.span ℂ (Set.range e) : Set C(X, ℂ)) ⊆
      (LinearMap.ker ((pairingCLM ν (star f)) : C(X, ℂ) →ₗ[ℂ] ℂ) : Set C(X, ℂ)) := by
    apply SetLike.coe_subset_coe.mpr
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pairingCLM_apply]
    have h := hf i
    unfold fourierCoeff at h
    have : ∫ x, e i x * (star f) x ∂ν = star (∫ x, f x * star (e i x) ∂ν) := by
      rw [show star (∫ x, f x * star (e i x) ∂ν) =
          (starRingEnd ℂ) (∫ x, f x * star (e i x) ∂ν) from rfl, ← integral_conj]
      congr 1
      funext x
      simp [mul_comm]
    rw [this, h, star_zero]
  have hclosed : IsClosed (LinearMap.ker ((pairingCLM ν (star f)) : C(X, ℂ) →ₗ[ℂ] ℂ) :
      Set C(X, ℂ)) := (pairingCLM ν (star f)).isClosed_ker
  have hmem : f ∈ LinearMap.ker ((pairingCLM ν (star f)) : C(X, ℂ) →ₗ[ℂ] ℂ) := by
    have htop := characterAlgebra_topologicalClosure he hsep
    have hf' : f ∈ (characterAlgebra he).topologicalClosure := by rw [htop]; trivial
    rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, characterAlgebra_coe] at hf'
    exact (closure_minimal hker hclosed) hf'
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pairingCLM_apply] at hmem
  have hsq : (fun x => f x * (star f) x) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    simp only [ContinuousMap.star_apply, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hsq] at hmem
  have hmem' : ((∫ x, ‖f x‖ ^ 2 ∂ν : ℝ) : ℂ) = 0 := by
    rw [← hmem]
    exact integral_ofReal.symm
  replace hmem := Complex.ofReal_eq_zero.mp hmem'
  have hcont : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have hint : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    integrable_continuousMap ν (⟨_, hcont⟩ : C(X, ℝ))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp hmem
  have heq : (fun x => ‖f x‖ ^ 2) = fun _ => (0 : ℝ) :=
    (hcont.ae_eq_iff_eq ν continuous_const).mp hae
  ext x
  have := congrFun heq x
  simpa using this

omit [CompactSpace X] [T2Space X] [BorelSpace X] [ν.IsOpenPosMeasure] in
open scoped Classical in
theorem integral_mul_star (he : IsCharacterFamily e) (horth : ∀ i, i ≠ 0 → ∫ x, e i x ∂ν = 0)
    (i j : ι) : ∫ x, e i x * star (e j x) ∂ν = if i = j then 1 else 0 := by
  have hprod : (fun x => e i x * star (e j x)) = fun x => e (i + -j) x := by
    funext x
    rw [he.add, he.neg]
    rfl
  rw [hprod]
  split_ifs with hij
  · subst hij
    rw [add_neg_cancel, he.zero]
    simp
  · exact horth _ (fun h => hij (by rwa [← sub_eq_add_neg, sub_eq_zero] at h))

open scoped Classical in
/-- Fourier inversion for absolutely summable Fourier coefficients. -/
theorem hasSum_fourierCoeff (he : IsCharacterFamily e)
    (hsep : ∀ x y : X, x ≠ y → ∃ i, e i x ≠ e i y)
    (horth : ∀ i, i ≠ 0 → ∫ x, e i x ∂ν = 0) (f : C(X, ℂ))
    (hsum : Summable fun i => ‖fourierCoeff ν e f i‖) (x : X) :
    HasSum (fun i => fourierCoeff ν e f i * e i x) (f x) := by
  set c := fourierCoeff ν e f with hc
  have hnorm : ∀ i, ‖c i • e i‖ ≤ ‖c i‖ := by
    intro i
    rw [norm_smul]
    have : ‖e i‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr fun x =>
      (he.norm_apply i x).le
    calc ‖c i‖ * ‖e i‖ ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖c i‖ := mul_one _
  have hs : Summable fun i => c i • e i := Summable.of_norm_bounded hsum hnorm
  set g := ∑' i, c i • e i with hg
  have hcoeff : ∀ j, fourierCoeff ν e g j = c j := by
    intro j
    have h1 : fourierCoeff ν e g j = pairingCLM ν (star (e j)) g := rfl
    rw [h1, hg, ContinuousLinearMap.map_tsum _ hs]
    have h2 : ∀ i, pairingCLM ν (star (e j)) (c i • e i) = if i = j then c i else 0 := by
      intro i
      rw [map_smul, pairingCLM_apply]
      have : ∫ x, e i x * (star (e j)) x ∂ν = ∫ x, e i x * star (e j x) ∂ν := rfl
      rw [this, integral_mul_star ν he horth i j]
      split_ifs <;> simp
    simp_rw [h2]
    exact tsum_ite_eq j (c)
  have hfg : f - g = 0 := by
    apply eq_zero_of_fourierCoeff_eq_zero ν he hsep
    intro j
    have : fourierCoeff ν e (f - g) j = fourierCoeff ν e f j - fourierCoeff ν e g j := by
      unfold fourierCoeff
      have i1 : Integrable (fun x => f x * star (e j x)) ν :=
        integrable_continuousMap ν (f * star (e j))
      have i2 : Integrable (fun x => g x * star (e j x)) ν :=
        integrable_continuousMap ν (g * star (e j))
      rw [← integral_sub i1 i2]
      congr 1
      funext x
      simp [sub_mul]
    rw [this, hcoeff, ← hc, sub_self]
  have hfg' : f = g := sub_eq_zero.mp hfg
  have hx := hs.hasSum.map (ContinuousMap.evalCLM ℂ x) (ContinuousMap.evalCLM ℂ x).continuous
  rw [hfg']
  simpa [Function.comp_def] using hx

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
