import Langlands.Global.GlobalPlaceTopologyFacts
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-! # Explicit nonunit sequences in actual adelic rings -/

noncomputable section

universe u v

open Filter Topology
open scoped Classical RestrictedProduct

namespace Langlands.Global

section Restricted

variable {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (A : ∀ i, Subring (R i))

/-- The integral tuple that is zero at one place and one at every other place. -/
def integralZeroAtPlace (i : ι) : ∀ j, A j := fun j => if j = i then 0 else 1

/-- Its image in the original cofinite restricted product. -/
def restrictedZeroAtPlace (i : ι) : Πʳ j, [R j, A j] :=
  RestrictedProduct.inclusion R (fun j => (A j : Set (R j))) le_top
    (RestrictedProduct.homeoTop (R := R) (A := fun j => (A j : Set (R j)))
      (integralZeroAtPlace A i))

@[simp]
theorem restrictedZeroAtPlace_apply (i j : ι) :
    restrictedZeroAtPlace A i j = if j = i then 0 else 1 := by
  classical
  change (↑(if j = i then (0 : A j) else 1) : R j) = _
  split <;> rfl

/-- A zero component witnesses failure of invertibility in the actual ring. -/
theorem restrictedZeroAtPlace_not_isUnit [∀ i, Nontrivial (R i)] (i : ι) :
    ¬ IsUnit (restrictedZeroAtPlace A i) := by
  intro h
  have hu := h.map (RestrictedProduct.evalRingHom R i)
  have hz : RestrictedProduct.evalRingHom R i (restrictedZeroAtPlace A i) = 0 := by
    simp [RestrictedProduct.evalRingHom_apply]
  rw [hz] at hu
  exact not_isUnit_zero hu

/-- Distinct zero positions converge to the all-one tuple in the integral product. -/
theorem tendsto_integralZeroAtPlace (e : ℕ ↪ ι) :
    Tendsto (fun n => integralZeroAtPlace A (e n)) atTop (𝓝 1) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro j
  have he : ∀ᶠ n : ℕ in atTop, e n ≠ j := by
    simpa only [Nat.cofinite_eq_atTop] using
      e.injective.tendsto_cofinite.eventually (show ∀ᶠ i : ι in cofinite, i ≠ j by simp)
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp [integralZeroAtPlace, Ne.symm hn]

/-- The convergence takes place in the restricted-product topology. -/
theorem tendsto_restrictedZeroAtPlace (e : ℕ ↪ ι) :
    Tendsto (fun n => restrictedZeroAtPlace A (e n)) atTop (𝓝 1) := by
  have hc : Continuous (fun x : ∀ j, A j =>
      RestrictedProduct.inclusion R (fun j => (A j : Set (R j)))
        (le_top : (cofinite : Filter ι) ≤ ⊤)
        (RestrictedProduct.homeoTop (R := R) (A := fun j => (A j : Set (R j))) x)) :=
    (RestrictedProduct.continuous_inclusion (le_top : (cofinite : Filter ι) ≤ ⊤)).comp
      (RestrictedProduct.homeoTop (R := R) (A := fun j => (A j : Set (R j)))).continuous
  have h := hc.continuousAt.tendsto.comp (tendsto_integralZeroAtPlace A e)
  exact h

end Restricted

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- An explicit sequence of pairwise distinct actual finite places. -/
def numberFieldNonunitPlaceSequence : ℕ ↪ FinitePlace K := by
  let : Infinite (FinitePlace K) := numberField_finitePlaces_infinite K
  exact Infinite.natEmbedding _

/-- All infinite coordinates are one; exactly one finite coordinate is zero. -/
def numberFieldNonunitSequence (n : ℕ) : Adeles K :=
  (1, restrictedZeroAtPlace
    (fun v : FinitePlace K => (v.adicCompletionIntegers K).toSubring)
    (numberFieldNonunitPlaceSequence K n))

theorem numberFieldNonunitSequence_not_isUnit (n : ℕ) :
    ¬ IsUnit (numberFieldNonunitSequence K n) := by
  intro h
  exact restrictedZeroAtPlace_not_isUnit _ _
    (h.map (RingHom.snd (InfiniteAdeles K) (FiniteAdeles K)))

theorem tendsto_numberFieldNonunitSequence :
    Tendsto (numberFieldNonunitSequence K) atTop (𝓝 1) := by
  exact tendsto_const_nhds.prodMk_nhds
    (tendsto_restrictedZeroAtPlace _ (numberFieldNonunitPlaceSequence K))

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Pairwise distinct actual discrete places, without a separability hypothesis. -/
def curvePlaceNonunitPlaceSequence : ℕ ↪ AlgebraicCurve.Place k F := by
  let : Infinite (AlgebraicCurve.Place k F) := functionField_places_infinite k F
  exact Infinite.natEmbedding _

/-- An actual function-field adele with one zero and all other coordinates one. -/
def curvePlaceNonunitSequence (n : ℕ) : CurvePlaceAdeleRing k F :=
  restrictedZeroAtPlace (fun v : AlgebraicCurve.Place k F =>
    (curvePlaceCompletionIntegers v).toSubring) (curvePlaceNonunitPlaceSequence k F n)

theorem curvePlaceNonunitSequence_not_isUnit (n : ℕ) :
    ¬ IsUnit (curvePlaceNonunitSequence k F n) :=
  restrictedZeroAtPlace_not_isUnit _ _

theorem tendsto_curvePlaceNonunitSequence :
    Tendsto (curvePlaceNonunitSequence k F) atTop (𝓝 1) :=
  tendsto_restrictedZeroAtPlace _ (curvePlaceNonunitPlaceSequence k F)

end Curve

end Langlands.Global
