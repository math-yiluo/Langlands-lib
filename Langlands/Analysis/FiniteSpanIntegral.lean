import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Noetherian.Basic

/-! # Integration in a finite-dimensional algebraic span -/

noncomputable section
universe uX uY uV uW
set_option autoImplicit false

namespace Langlands.Analysis.FiniteSpanIntegral

open MeasureTheory
open scoped BigOperators

variable {X : Type uX} [TopologicalSpace X]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A map with finite-dimensional algebraic span and continuous scalar coefficients. -/
def HasFiniteContinuousSpan (F : X → V) : Prop :=
  (Submodule.span ℂ (Set.range F)).FG ∧
    ∀ l : Module.Dual ℂ V, Continuous (fun x => l (F x))

theorem HasFiniteContinuousSpan.const (v : V) :
    HasFiniteContinuousSpan (fun _ : X => v) := by
  refine ⟨(Submodule.fg_span_singleton v).of_le ?_, fun _ => continuous_const⟩
  apply Submodule.span_mono
  rintro _ ⟨x, rfl⟩
  exact Set.mem_singleton v

theorem HasFiniteContinuousSpan.add {F H : X → V}
    (hF : HasFiniteContinuousSpan F) (hH : HasFiniteContinuousSpan H) :
    HasFiniteContinuousSpan (fun x => F x + H x) := by
  refine ⟨(hF.1.sup hH.1).of_le (Submodule.span_le.mpr ?_), ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨x, rfl⟩)
      (Submodule.subset_span ⟨x, rfl⟩)
  · intro l
    convert (hF.2 l).add (hH.2 l) using 1
    ext x
    exact l.map_add (F x) (H x)

/-- Finite span and scalar continuity pass through every algebraic linear map. -/
theorem HasFiniteContinuousSpan.linearMap {F : X → V} (hF : HasFiniteContinuousSpan F)
    (L : V →ₗ[ℂ] W) : HasFiniteContinuousSpan (fun x => L (F x)) := by
  refine ⟨?_, fun l => hF.2 (l.comp L)⟩
  have hr : Set.range (fun x => L (F x)) = L '' Set.range F := by
    ext w
    simp
  rw [hr, ← Submodule.map_span]
  exact hF.1.map L

theorem HasFiniteContinuousSpan.smul {F : X → V} (hF : HasFiniteContinuousSpan F) (c : ℂ) :
    HasFiniteContinuousSpan (fun x => c • F x) :=
  hF.linearMap (c • (LinearMap.id : V →ₗ[ℂ] V))

theorem HasFiniteContinuousSpan.comp {Y : Type uY} [TopologicalSpace Y] {F : X → V}
    (hF : HasFiniteContinuousSpan F) (p : Y → X) (hp : Continuous p) :
    HasFiniteContinuousSpan (fun y => F (p y)) := by
  refine ⟨hF.1.of_le (Submodule.span_mono ?_), fun l => (hF.2 l).comp hp⟩
  rintro _ ⟨y, rfl⟩
  exact ⟨p y, rfl⟩

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem HasFiniteContinuousSpan.integrable_dual {F : X → V}
    (hF : HasFiniteContinuousSpan F) (l : Module.Dual ℂ V) :
    Integrable (fun x => l (F x)) μ :=
  (hF.2 l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Scalar integration is represented by a vector in the finite algebraic span. -/
theorem exists_integral {F : X → V} (hF : HasFiniteContinuousSpan F) :
    ∃ v : V, ∀ l : Module.Dual ℂ V, l v = ∫ x, l (F x) ∂μ := by
  classical
  let P := Submodule.span ℂ (Set.range F)
  let : Module.Finite ℂ P := Module.Finite.of_fg hF.1
  let b := Module.finBasis ℂ P
  let F' (x : X) : P := ⟨F x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hq (i : Fin (Module.finrank ℂ P)) :
      ∃ q : Module.Dual ℂ V, q.comp P.subtype = b.coord i :=
    (b.coord i).exists_extend
  choose q hq using hq
  have hqF (i : Fin (Module.finrank ℂ P)) (x : X) :
      q i (F x) = b.repr (F' x) i :=
    LinearMap.congr_fun (hq i) (F' x)
  refine ⟨P.subtype (∑ i, (∫ x, q i (F x) ∂μ) • b i), ?_⟩
  intro l
  have hexp (x : X) : l (F x) = ∑ i, q i (F x) * l (b i : V) := by
    have h := congrArg (fun y : P => l (P.subtype y)) (b.sum_repr (F' x))
    simpa only [map_sum, map_smul, smul_eq_mul, F', Submodule.subtype_apply, hqF] using h.symm
  simp only [map_sum, map_smul, smul_eq_mul, Submodule.subtype_apply]
  simp_rw [hexp]
  have hI (i : Fin (Module.finrank ℂ P)) :
      Integrable (fun x => q i (F x) * l (b i : V)) μ :=
    ((hF.2 (q i)).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum Finset.univ (fun i _ => hI i)]
  simp only [integral_mul_const]

/-- The vector representing integration of all scalar coefficients. -/
def integral (F : X → V) (hF : HasFiniteContinuousSpan F) : V :=
  (exists_integral μ hF).choose

@[simp]
theorem dual_integral (F : X → V) (hF : HasFiniteContinuousSpan F) (l : Module.Dual ℂ V) :
    l (integral μ F hF) = ∫ x, l (F x) ∂μ :=
  (exists_integral μ hF).choose_spec l

/-- Algebraic linear functionals separate vectors, without an ambient topology. -/
theorem eq_of_dual_eq {v w : V} (h : ∀ l : Module.Dual ℂ V, l v = l w) : v = w := by
  by_contra hne
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hne)
  exact hl (by rw [map_sub, h l, sub_self])

theorem integral_eq_iff (F : X → V) (hF : HasFiniteContinuousSpan F) (v : V) :
    integral μ F hF = v ↔ ∀ l : Module.Dual ℂ V, (∫ x, l (F x) ∂μ) = l v := by
  constructor
  · intro h l
    rw [← dual_integral μ F hF l, h]
  · intro h
    exact eq_of_dual_eq fun l => (dual_integral μ F hF l).trans (h l)

/-- Integration commutes with every linear map; no topology on either carrier is required. -/
theorem integral_linearMap (F : X → V) (hF : HasFiniteContinuousSpan F) (L : V →ₗ[ℂ] W) :
    integral μ (fun x => L (F x)) (hF.linearMap L) = L (integral μ F hF) := by
  apply eq_of_dual_eq
  intro l
  rw [dual_integral]
  exact (dual_integral μ F hF (l.comp L)).symm

theorem integral_add (F H : X → V) (hF : HasFiniteContinuousSpan F)
    (hH : HasFiniteContinuousSpan H) :
    integral μ (fun x => F x + H x) (hF.add hH) =
      integral μ F hF + integral μ H hH := by
  apply eq_of_dual_eq
  intro l
  simp only [dual_integral, map_add]
  exact MeasureTheory.integral_add (hF.integrable_dual μ l) (hH.integrable_dual μ l)

theorem integral_smul (F : X → V) (hF : HasFiniteContinuousSpan F) (c : ℂ) :
    integral μ (fun x => c • F x) (hF.smul c) = c • integral μ F hF := by
  apply eq_of_dual_eq
  intro l
  simp only [dual_integral, map_smul]
  exact MeasureTheory.integral_smul c (fun x => l (F x))

theorem integral_const (v : V) :
    integral μ (fun _ : X => v) (HasFiniteContinuousSpan.const v) =
      (μ.real Set.univ : ℂ) • v := by
  apply eq_of_dual_eq
  intro l
  simp [dual_integral, MeasureTheory.integral_const, Complex.real_smul]

theorem integral_const_of_probability [IsProbabilityMeasure μ] (v : V) :
    integral μ (fun _ : X => v) (HasFiniteContinuousSpan.const v) = v := by
  simpa using integral_const μ v

end Langlands.Analysis.FiniteSpanIntegral
