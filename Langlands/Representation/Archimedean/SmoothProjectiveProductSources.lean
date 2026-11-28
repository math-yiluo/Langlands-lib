import Langlands.Representation.Archimedean.SmoothLieActionUnits
import Langlands.Representation.Archimedean.SmoothProjectiveProductDensity

/-! # Dense source subspaces for smooth projective products -/

noncomputable section

open Set
open scoped ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Archimedean.CompletedProjectiveRepresentation

open DerivativeSmoothVectors

universe uι uA uE uF

variable {ι : Type uι} [Fintype ι]
  (A : ι → Type uA) [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℝ (A i)]
  [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional ℝ (A i)]
  {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, (A i)ˣ →* (E i →L[ℂ] E i))

local notation "I" => 𝓘(ℝ, (∀ i, A i))
local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "D₀" => fun i => DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)

/-- The pure tensor map is continuous for the full word-derivative topology of the product. -/
theorem continuous_pureSmooth (hR : ∀ i, IsContinuousRepresentation (R i)) :
    Continuous (pureSmooth A R) := by
  classical
  have hP := isContinuous_productAction A R hR
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  change Continuous (fun v : ∀ i, D₀ i => derivativeCoordinates I P (pureSmooth A R v) Xs)
  induction Xs using List.reverseRecOn with
  | nil =>
    change Continuous (fun v : ∀ i, D₀ i => pure E (fun i => derivativeCLM 𝓘(ℝ, A i) (R i) [] (v i)))
    exact (pure E).cont.comp (continuous_pi fun i =>
      (derivativeCLM 𝓘(ℝ, A i) (R i) []).continuous.comp (continuous_apply i))
  | append_singleton Xs X ih =>
    have hOp (v : D) : operator I P X v = ∑ i, operator I P (Pi.single i (X i)) v := by
      change operatorDirection P X v = ∑ i, operatorDirection P (Pi.single i (X i)) v
      rw [← LinearMap.sum_apply, ← map_sum, LinearMap.sum_single_apply]
    have hUpdate (i : ι) : Continuous (fun v : ∀ j, D₀ j =>
        Function.update v i (operator 𝓘(ℝ, A i) (R i) (X i) (v i))) := by
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        simp only [Function.update_self]
        exact (continuous_operator 𝓘(ℝ, A i) (R i) (X i)).comp (continuous_apply i)
      · simpa only [Function.update_of_ne h] using (continuous_apply (A := D₀) j)
    conv in derivativeCoordinates I P (pureSmooth A R _) (Xs ++ [X]) =>
      rw [← derivativeCoordinates_operator]
    simp_rw [hOp, map_sum, Finset.sum_apply, operator_axial_pureSmooth A R hP hR]
    exact continuous_finsetSum _ fun i _ => ih.comp (hUpdate i)

/-- Applying the pure map to any dense source in each factor gives a dense span in the
product smooth carrier. -/
def SmoothProjectiveProductSourcesStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (F : ι → Type uF) (f : ∀ i, F i → D₀ i), (∀ i, DenseRange (f i)) →
    Dense (Submodule.span ℂ (range (fun x : ∀ i, F i => pureSmooth A R (fun i => f i (x i)))) : Set D)

theorem smoothProjectiveProductSources : SmoothProjectiveProductSourcesStatement A R := by
  intro hR F f hf
  let W := Submodule.span ℂ (range (fun x : ∀ i, F i => pureSmooth A R (fun i => f i (x i))))
  have hp : MapsTo (pureSmooth A R) (range (Pi.map f)) W.topologicalClosure := by
    rintro _ ⟨v, rfl⟩
    exact W.le_topologicalClosure (Submodule.subset_span (mem_range_self v))
  have hDense : DenseRange (Pi.map f) := DenseRange.piMap hf
  have hSpan : pureSmoothSpan A R ≤ W.topologicalClosure := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, rfl⟩
    exact hp.closure_left (continuous_pureSmooth A R hR) W.isClosed_topologicalClosure (hDense v)
  intro v
  exact closure_minimal hSpan W.isClosed_topologicalClosure (smoothProjectiveProductDensity A E R hR v)

end Langlands.Archimedean.CompletedProjectiveRepresentation
