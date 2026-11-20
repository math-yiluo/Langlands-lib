import Langlands.Representation.Whittaker.Algebraic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite spans under left and right translation -/

noncomputable section

open Set
open scoped Classical

set_option autoImplicit false

namespace Langlands.Archimedean.FiniteTranslationSpan

variable {K : Type*} [Group K]
open Langlands.Whittaker (rightTranslation)

/-- The span of right translates of one function. -/
def rightSpan (f : K → ℂ) : Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ (range fun k : K => rightTranslation ℂ K k f)

/-- The span of all simultaneous left and right translates of one function. -/
def twoSidedSpan (f : K → ℂ) : Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ (range fun x : K × K => fun k => f (x.1 * k * x.2))

theorem mem_twoSidedSpan (f : K → ℂ) : f ∈ twoSidedSpan f :=
  Submodule.subset_span ⟨(1, 1), funext fun k => by simp⟩

private def translate (x y : K) : (K → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun f k := f (x * k * y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem translate_mem_twoSidedSpan {f v : K → ℂ} (hv : v ∈ twoSidedSpan f) (x y : K) :
    (fun k => v (x * k * y)) ∈ twoSidedSpan f := by
  have h : twoSidedSpan f ≤ (twoSidedSpan f).comap (translate x y) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    exact Submodule.subset_span ⟨(u * x, y * w), funext fun k => by simp [translate, mul_assoc]⟩
  exact h hv

/-- Right translation preserves the span of all right translates. -/
theorem rightTranslation_mem_rightSpan {f v : K → ℂ} (hv : v ∈ rightSpan f) (x : K) :
    rightTranslation ℂ K x v ∈ rightSpan f := by
  have h : rightSpan f ≤ (rightSpan f).comap (rightTranslation ℂ K x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    exact Submodule.subset_span ⟨x * y, funext fun k => by
      change f (k * (x * y)) = f (k * x * y)
      rw [mul_assoc]⟩
  exact h hv

/-- Right translation as an operator on a right-stable subspace. -/
def rightOn (V : Submodule ℂ (K → ℂ))
    (hV : ∀ (x : K) (f : V), rightTranslation ℂ K x f.val ∈ V) (x : K) : V →ₗ[ℂ] V :=
  ((rightTranslation ℂ K x).comp V.subtype).codRestrict V (hV x)

/-- The matrix coefficient of a vector in a right-stable function space. -/
def coefficient (V : Submodule ℂ (K → ℂ))
    (hV : ∀ (x : K) (f : V), rightTranslation ℂ K x f.val ∈ V) (v : V) :
    Module.Dual ℂ V →ₗ[ℂ] (K → ℂ) :=
  LinearMap.pi fun x => Module.Dual.eval ℂ V (rightOn V hV x v)

private def eval (V : Submodule ℂ (K → ℂ)) (x : K) : Module.Dual ℂ V :=
  (LinearMap.proj (R := ℂ) x).comp V.subtype

omit [Group K] in
private theorem eval_span_eq_top (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (range (eval V)) = ⊤ := by
  let A := Submodule.span ℂ (range (eval V))
  refine le_antisymm le_top fun ℓ _ => ?_
  change ℓ ∈ A
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := A), Submodule.mem_dualAnnihilator]
  intro v hv
  have hv0 : v = 0 := by
    apply Subtype.ext
    funext x
    exact (Submodule.mem_dualCoannihilator v).mp hv (eval V x) (Submodule.subset_span ⟨x, rfl⟩)
  simp [hv0]

/-- In a finite-dimensional subspace stable under both translations, its coefficients remain in it. -/
theorem coefficient_mem {V : Submodule ℂ (K → ℂ)} [FiniteDimensional ℂ V]
    (hr : ∀ (x : K) (f : V), rightTranslation ℂ K x f.val ∈ V)
    (hl : ∀ (x : K) (f : V), (fun k => f.val (x * k)) ∈ V)
    (v : V) (ℓ : Module.Dual ℂ V) : coefficient V hr v ℓ ∈ V := by
  have h : Submodule.span ℂ (range (eval V)) ≤ V.comap (coefficient V hr v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hl x v
  exact h (by rw [eval_span_eq_top]; exact Submodule.mem_top)

theorem finiteDimensional_twoSidedSpan (f : K → ℂ) [FiniteDimensional ℂ (rightSpan f)] :
    FiniteDimensional ℂ (twoSidedSpan f) := by
  let V := rightSpan f
  have hV (x : K) (v : V) : rightTranslation ℂ K x v.val ∈ V := rightTranslation_mem_rightSpan v.2 x
  let e := Module.Free.chooseBasis ℂ V
  let M i := coefficient V hV (e i)
  let W : Submodule ℂ (K → ℂ) := ⨆ i, LinearMap.range (M i)
  have : FiniteDimensional ℂ W := by
    dsimp only [W]
    infer_instance
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, y⟩, rfl⟩
  let v : V := ⟨rightTranslation ℂ K y f, Submodule.subset_span ⟨y, rfl⟩⟩
  have he : (fun k => f (x * k * y)) = ∑ i, e.repr v i • M i (eval V x) := by
    funext k
    rw [Finset.sum_apply]
    let L := (eval V x).comp (rightOn V hV k)
    change L v = ∑ i, e.repr v i • L (e i)
    conv_lhs => rw [← e.sum_repr v]
    simp only [map_sum, map_smul]
  change (fun k => f (x * k * y)) ∈ W
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem W _
    (le_iSup (fun i => LinearMap.range (M i)) i (LinearMap.mem_range_self _ _))

/-- A finite right translate span yields a finite two-sided translate span. -/
def FiniteTranslationSpanStatement : Prop :=
  ∀ (K : Type*) [Group K] (f : K → ℂ),
    FiniteDimensional ℂ (rightSpan f) → FiniteDimensional ℂ (twoSidedSpan f)

theorem finiteTranslationSpan : FiniteTranslationSpanStatement := by
  intro K hK f hf
  let : FiniteDimensional ℂ (rightSpan f) := hf
  exact finiteDimensional_twoSidedSpan f

end Langlands.Archimedean.FiniteTranslationSpan
