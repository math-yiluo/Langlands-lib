import Langlands.Global.GlobalPlaceTopologyFacts
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-! # Actual adelic units with divergent inverses -/

noncomputable section

universe u v

open Filter Topology
open scoped Classical RestrictedProduct

namespace Langlands.Global

section Restricted

variable {ι : Type u} {R : ι → Type v} [∀ i, Field (R i)]
    [∀ i, TopologicalSpace (R i)] (A : ∀ i, Subring (R i))
    (a : ∀ i, A i) (ha : ∀ i, (a i : R i) ≠ 0)

/-- A unit with the chosen integral value at one place and one elsewhere. -/
def restrictedUnitAtPlace (i : ι) : (Πʳ j, [R j, A j])ˣ :=
  RestrictedProduct.mkUnit
    (fun j => if j = i then Units.mk0 (a j : R j) (ha j) else 1) (by
      filter_upwards [show ∀ᶠ j : ι in cofinite, j ≠ i by simp] with j hj
      simpa only [ite_eq_right hj] using
        (one_mem ((Submonoid.ofClass (A j)).units)))

omit [∀ i, TopologicalSpace (R i)] in
@[simp] theorem restrictedUnitAtPlace_val_apply (i j : ι) :
    ((restrictedUnitAtPlace A a ha i : (Πʳ j, [R j, A j])ˣ) :
      Πʳ j, [R j, A j]) j = if j = i then (a j : R j) else 1 := by
  change (↑(if j = i then Units.mk0 (a j : R j) (ha j) else 1) : R j) = _
  split <;> rfl

omit [∀ i, TopologicalSpace (R i)] in
@[simp] theorem restrictedUnitAtPlace_inv_apply (i : ι) :
    (((restrictedUnitAtPlace A a ha i)⁻¹ : (Πʳ j, [R j, A j])ˣ) :
      Πʳ j, [R j, A j]) i = (a i : R i)⁻¹ := by
  change (↑((if i = i then Units.mk0 (a i : R i) (ha i) else 1)⁻¹) : R i) = _
  simp

/-- Distinct exceptional places give convergence in the original adelic topology. -/
theorem tendsto_restrictedUnitAtPlace_val (e : ℕ ↪ ι) :
    Tendsto (fun n => ((restrictedUnitAtPlace A a ha (e n)) :
      Πʳ j, [R j, A j])) atTop (𝓝 1) := by
  let x : ℕ → ∀ j, A j := fun n j => if j = e n then a j else 1
  have hx : Tendsto x atTop (𝓝 1) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have he : ∀ᶠ n : ℕ in atTop, e n ≠ j := by
      simpa only [Nat.cofinite_eq_atTop] using
        e.injective.tendsto_cofinite.eventually
          (show ∀ᶠ i : ι in cofinite, i ≠ j by simp)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp [x, Ne.symm hn]
  let f : (∀ j, A j) → Πʳ j, [R j, A j] := fun b =>
    RestrictedProduct.inclusion R (fun j => (A j : Set (R j))) le_top
      (RestrictedProduct.homeoTop (R := R) (A := fun j => (A j : Set (R j))) b)
  have hf : Continuous f :=
    (RestrictedProduct.continuous_inclusion (le_top : (cofinite : Filter ι) ≤ ⊤)).comp
      (RestrictedProduct.homeoTop (R := R) (A := fun j => (A j : Set (R j)))).continuous
  have heq (n : ℕ) : f (x n) =
      ((restrictedUnitAtPlace A a ha (e n)) : Πʳ j, [R j, A j]) := by
    ext j
    rw [restrictedUnitAtPlace_val_apply]
    change (↑(if j = e n then a j else 1) : R j) = _
    split <;> rfl
  have hf1 : f 1 = 1 := by ext j; rfl
  simpa only [Function.comp_def, heq, hf1] using hf.continuousAt.tendsto.comp hx

/-- Nonintegral inverse coordinates prevent convergence of the inverse adeles. -/
theorem not_tendsto_restrictedUnitAtPlace_inv
    (hA : ∀ i, IsOpen (A i : Set (R i)))
    (hi : ∀ i, (a i : R i)⁻¹ ∉ A i) (e : ℕ ↪ ι) :
    ¬ Tendsto (fun n => Units.val ((restrictedUnitAtPlace A a ha (e n))⁻¹))
      atTop (𝓝 1) := by
  intro ht
  have hn : {b : Πʳ j, [R j, A j] | ∀ j, b j ∈ A j} ∈
      𝓝 (1 : Πʳ j, [R j, A j]) :=
    (RestrictedProduct.isOpen_forall_mem hA).mem_nhds (fun j => (A j).one_mem)
  have he := ht.eventually hn
  obtain ⟨n, hn⟩ := he.exists
  exact hi (e n) (by simpa only [restrictedUnitAtPlace_inv_apply] using hn (e n))

end Restricted

section Adic

variable {B : Type u} [CommRing B] [IsDedekindDomain B]
    (K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]
    (v : IsDedekindDomain.HeightOneSpectrum B)

/-- A uniformizer in the actual completed valuation ring. -/
def adicIntegralNonunit : v.adicCompletionIntegers K :=
  ⟨algebraMap K (v.adicCompletion K)
      (Classical.choose (v.valuation_exists_uniformizer K)), by
    change Valued.v (algebraMap K (v.adicCompletion K)
      (Classical.choose (v.valuation_exists_uniformizer K))) ≤
        (1 : WithZero (Multiplicative ℤ))
    simp only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Classical.choose_spec (v.valuation_exists_uniformizer K)]
    simp⟩

theorem adicIntegralNonunit_ne_zero : (adicIntegralNonunit K v : v.adicCompletion K) ≠ 0 :=
  (map_ne_zero (algebraMap K (v.adicCompletion K))).mpr
    (v.valuation_uniformizer_ne_zero K)

theorem adicIntegralNonunit_inv_not_mem :
    (adicIntegralNonunit K v : v.adicCompletion K)⁻¹ ∉ v.adicCompletionIntegers K := by
  change ¬ Valued.v ((adicIntegralNonunit K v : v.adicCompletion K)⁻¹) ≤
    (1 : WithZero (Multiplicative ℤ))
  simp only [adicIntegralNonunit, map_inv₀,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    Classical.choose_spec (v.valuation_exists_uniformizer K)]
  simp

end Adic

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Distinct actual finite places used for the unit sequence. -/
def numberFieldUnitPlaceSequence : ℕ ↪ FinitePlace K := by
  let : Infinite (FinitePlace K) := numberField_finitePlaces_infinite K
  exact Infinite.natEmbedding _

/-- All archimedean coordinates are one; one finite coordinate is a uniformizer. -/
def numberFieldUnitSequence (n : ℕ) : (Adeles K)ˣ :=
  (MulEquiv.prodUnits : (Adeles K)ˣ ≃* (InfiniteAdeles K)ˣ × (FiniteAdeles K)ˣ).symm
    (1, restrictedUnitAtPlace
      (fun v : FinitePlace K => (v.adicCompletionIntegers K).toSubring)
      (fun v => adicIntegralNonunit K v) (fun v => adicIntegralNonunit_ne_zero K v)
      (numberFieldUnitPlaceSequence K n))

theorem tendsto_numberFieldUnitSequence_val :
    Tendsto (fun n => (numberFieldUnitSequence K n : Adeles K)) atTop (𝓝 1) :=
  tendsto_const_nhds.prodMk_nhds
    (tendsto_restrictedUnitAtPlace_val _ _ _ (numberFieldUnitPlaceSequence K))

theorem not_tendsto_numberFieldUnitSequence_inv :
    ¬ Tendsto (fun n => Units.val ((numberFieldUnitSequence K n)⁻¹)) atTop (𝓝 1) := by
  intro ht
  exact not_tendsto_restrictedUnitAtPlace_inv _ _ _
    (fun v : FinitePlace K => Valued.isOpen_valuationSubring (v.adicCompletion K))
    (fun v => adicIntegralNonunit_inv_not_mem K v) (numberFieldUnitPlaceSequence K)
    ((continuous_snd.tendsto (1 : Adeles K)).comp ht)

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Distinct actual discrete curve places, allowing inseparable function fields. -/
def curvePlaceUnitPlaceSequence : ℕ ↪ AlgebraicCurve.Place k F := by
  let : Infinite (AlgebraicCurve.Place k F) := functionField_places_infinite k F
  exact Infinite.natEmbedding _

/-- One uniformizer coordinate and otherwise one, in the actual adelic unit group. -/
def curvePlaceUnitSequence (n : ℕ) : (CurvePlaceAdeleRing k F)ˣ :=
  restrictedUnitAtPlace
    (fun v : AlgebraicCurve.Place k F => (curvePlaceCompletionIntegers v).toSubring)
    (fun v => adicIntegralNonunit F v.heightOneSpectrum)
    (fun v => adicIntegralNonunit_ne_zero F v.heightOneSpectrum)
    (curvePlaceUnitPlaceSequence k F n)

theorem tendsto_curvePlaceUnitSequence_val :
    Tendsto (fun n => (curvePlaceUnitSequence k F n : CurvePlaceAdeleRing k F))
      atTop (𝓝 1) :=
  tendsto_restrictedUnitAtPlace_val _ _ _ (curvePlaceUnitPlaceSequence k F)

theorem not_tendsto_curvePlaceUnitSequence_inv :
    ¬ Tendsto (fun n => Units.val ((curvePlaceUnitSequence k F n)⁻¹))
      atTop (𝓝 1) :=
  not_tendsto_restrictedUnitAtPlace_inv _ _ _
    (fun v : AlgebraicCurve.Place k F =>
      Valued.isOpen_valuationSubring (curvePlaceCompletion v))
    (fun v => adicIntegralNonunit_inv_not_mem F v.heightOneSpectrum)
    (curvePlaceUnitPlaceSequence k F)

end Curve

end Langlands.Global
