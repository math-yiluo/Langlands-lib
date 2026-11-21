import Langlands.Global.ArchimedeanSmoothFamilyAverage
import Langlands.Global.ArchimedeanSmoothFamilyOrbit
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Finite-rank compact averaging after simultaneous translation -/

noncomputable section
universe u v
open MeasureTheory Set
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL.SmoothFamily

open DerivativeSmoothFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {ι : Type v}
local notation "V" => SmoothFamily F n ι
local notation "G" => InfiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n

private def pointEvaluations : V →ₗ[ℂ] (ι → G → ℂ) :=
  LinearMap.pi fun i => LinearMap.pi fun x => (evalCLM F n x).toLinearMap.comp (LinearMap.proj i)

private theorem pointEvaluations_apply (f : V) (i : ι) (x : G) :
    pointEvaluations f i x = evalCLM F n x (f i) := rfl

private theorem pointEvaluations_injective :
    Function.Injective (pointEvaluations (F := F) (n := n) (ι := ι)) := by
  intro f g h
  funext i
  apply (toSmooth F n).injective
  apply Subtype.ext
  funext x
  simpa only [pointEvaluations_apply, evalCLM_apply] using congrFun (congrFun h i) x

variable {J : Type u} [TopologicalSpace J] [T2Space J] [CompactSpace J]
  [MeasurableSpace J] [BorelSpace J]
  (r : C(J, InfiniteAdelicGL F n)) (ν : Measure J) [IsFiniteMeasure ν] (w : C(J, ℂ))

set_option maxHeartbeats 900000 in
private theorem continuous_average_pointEvaluation (i : ι) (x : G) :
    Continuous (fun f : V => pointEvaluations (averageLM r ν w f) i x) := by
  let c (f : V) := toContinuousMapCLM F n (f i)
  have hc : Continuous c := (toContinuousMapCLM F n).continuous.comp (continuous_apply i)
  let b (f : V) : C(J, ℂ) := ⟨fun j => w j * c f (x * r j),
    w.continuous.mul ((c f).continuous.comp (continuous_const.mul r.continuous))⟩
  have hb : Continuous b := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hpair : Continuous (fun p : V × J => (c p.1, x * r p.2)) :=
      (hc.comp continuous_fst).prodMk (continuous_const.mul (r.continuous.comp continuous_snd))
    exact (w.continuous.comp continuous_snd).mul (continuous_eval.comp hpair)
  have hI : Continuous (fun f : Lp ℂ 1 ν => ∫ j, f j ∂ν) := continuous_integral
  have hL := (ContinuousMap.toLp (E := ℂ) 1 ν ℂ).continuous
  apply (hI.comp (hL.comp hb)).congr
  intro f
  rw [pointEvaluations_apply, averageLM_apply, CompactIndexAverage.eval_averageLM]
  change (∫ j, ContinuousMap.toLp (E := ℂ) 1 ν ℂ (b f) j ∂ν) = ∫ j, b f j ∂ν
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ) ν (b f))

private theorem continuous_averagedPointEvaluations :
    Continuous (fun f : V => pointEvaluations (averageLM r ν w f)) :=
  continuous_pi fun i => continuous_pi fun x => continuous_average_pointEvaluation r ν w i x

private theorem averageLM_mem_of_compactOrbit (S : Submodule ℂ V)
    (hK : ∀ j : J, r j ∈ K) {f : V}
    (hfin : FiniteDimensional ℂ (Langlands.FiniteVectors.orbitSpan compactRepresentation f))
    (hm : ∀ k : K, compactRepresentation k f ∈ S) : averageLM r ν w f ∈ S := by
  let O := Langlands.FiniteVectors.orbitSpan compactRepresentation f
  have hO : O ≤ S := Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hm k)
  have ha : averageLM r ν w f ∈ O.topologicalClosure := by
    apply averageLM_mem_topologicalClosure r ν w O f
    intro j
    exact O.le_topologicalClosure
      (Langlands.FiniteVectors.action_mem_orbitSpan compactRepresentation ⟨r j, hK j⟩ f)
  rw [O.closed_of_finiteDimensional.submodule_topologicalClosure_eq] at ha
  exact hO ha

/-- A finite-rank compact average of a group translate belongs to the same submodule
when it is stable under compact and enveloping actions and has finite compact orbits. -/
theorem averagedTranslate_mem (S : Submodule ℂ V)
    (hstab : ∀ (k : K) (a : EnvelopingAlgebra F n) (f : V),
      f ∈ S → compactRepresentation k (a • f) ∈ S)
    (hK : ∀ j : J, r j ∈ K)
    (hfin : ∀ f ∈ S, FiniteDimensional ℂ (Langlands.FiniteVectors.orbitSpan compactRepresentation f))
    (hE : FiniteDimensional ℂ (S.map (averageLM r ν w))) {f : V} (hf : f ∈ S)
    (hjoint : ∀ i, IsJointFinite F n (toSmooth F n (f i))) (g : G) :
    averageLM r ν w (rightRepresentation g f) ∈ S := by
  let P : V →ₗ[ℂ] V := averageLM r ν w
  let E := S.map P
  have hES : E ≤ S := Submodule.map_le_iff_le_comap.mpr fun y hy =>
    averageLM_mem_of_compactOrbit r ν w S hK (hfin y hy) (fun k => by
      simpa only [one_smul] using hstab k 1 y hy)
  have hcont := continuous_averagedPointEvaluations r ν w (ι := ι)
  let A := E.map pointEvaluations
  have hA : IsClosed (A : Set (ι → G → ℂ)) := A.closed_of_finiteDimensional
  have hclosed : IsClosed {v : V | pointEvaluations (P v) ∈ A} := hA.preimage hcont
  have hsub : (S : Set V) ⊆ {v : V | pointEvaluations (P v) ∈ A} := fun v hv =>
    Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hv)
  have hg := rightRepresentation_mem_closure S f hjoint (fun k a => hstab k a f hf) g
  obtain ⟨z, hz, he⟩ := closure_minimal hsub hclosed hg
  exact hES (pointEvaluations_injective he ▸ hz)

/-- Compact averaging with finite-dimensional image on an algebraically stable submodule
carries translated joint-finite vectors back into the submodule. -/
def ArchimedeanCompactAverageTranslationStatement : Prop :=
  ∀ (S : Submodule ℂ V), (∀ (k : K) (a : EnvelopingAlgebra F n) (f : V),
    f ∈ S → compactRepresentation k (a • f) ∈ S) →
  (∀ j : J, r j ∈ K) →
  (∀ f ∈ S, FiniteDimensional ℂ (Langlands.FiniteVectors.orbitSpan compactRepresentation f)) →
  FiniteDimensional ℂ (S.map (averageLM r ν w)) →
  ∀ f ∈ S, (∀ i, IsJointFinite F n (toSmooth F n (f i))) → ∀ g : G,
    averageLM r ν w (rightRepresentation g f) ∈ S

theorem archimedeanCompactAverageTranslation : ArchimedeanCompactAverageTranslationStatement r ν w (ι := ι) := by
  intro S hstab hK hfin hE f hf hjoint g
  exact averagedTranslate_mem r ν w S hstab hK hfin hE hf hjoint g

end Langlands.Global.ArchimedeanGL.SmoothFamily
