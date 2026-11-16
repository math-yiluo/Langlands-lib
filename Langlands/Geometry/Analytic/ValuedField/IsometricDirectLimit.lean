import Langlands.Geometry.Analytic.Affinoid
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion

/-! # Direct limits of isometric systems of normed fields -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IsometricDirectLimit

variable {K : Type u} [NormedField K]
  {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (F : I → Type v) [∀ i, NormedField (F i)] [∀ i, NormedAlgebra K (F i)]
  (f : ∀ i j, i ≤ j → F i →ₐ[K] F j)
  [DirectedSystem F (f · · ·)]
  (hf : ∀ i j h, Isometry (f i j h))

/-- The common norm of a representative of the algebraic direct limit. -/
def value : DirectLimit F f → ℝ :=
  DirectLimit.lift f (fun _ x => ‖x‖) fun i j h x =>
    ((AddMonoidHomClass.isometry_iff_norm (f i j h)).mp (hf i j h) x).symm

omit [Nonempty I] in
@[simp]
theorem value_mk (i : I) (x : F i) : value F f hf ⟦⟨i, x⟩⟧ = ‖x‖ := rfl

/-- The representative norm defines an absolute value on the field direct limit. -/
def absoluteValue : AbsoluteValue (DirectLimit F f) ℝ where
  toFun := value F f hf
  map_mul' a b := by
    induction a, b using DirectLimit.induction₂ f with
    | _ i a b =>
      rw [DirectLimit.mul_def]
      exact norm_mul a b
  nonneg' a := by
    induction a using DirectLimit.induction f with
    | _ i a => exact norm_nonneg a
  eq_zero' a := by
    induction a using DirectLimit.induction f with
    | _ i a =>
      change ‖a‖ = 0 ↔ DirectLimit.Ring.of F f i a = 0
      rw [norm_eq_zero, map_eq_zero_iff (DirectLimit.Ring.of F f i)]
      exact (DirectLimit.Ring.of F f i).injective
  add_le' a b := by
    induction a, b using DirectLimit.induction₂ f with
    | _ i a b =>
      rw [DirectLimit.add_def]
      exact norm_add_le a b

@[simp]
theorem absoluteValue_mk (i : I) (x : F i) :
    absoluteValue F f hf ⟦⟨i, x⟩⟧ = ‖x‖ := rfl

/-- The normed direct limit of a directed system of isometric field embeddings. -/
abbrev Carrier := WithAbs (absoluteValue F f hf)

/-- The component algebra maps into the normed direct limit. -/
def of (i : I) : F i →ₐ[K] Carrier F f hf :=
  (WithAbs.algEquiv K (absoluteValue F f hf)).symm.toAlgHom.comp
    (DirectLimit.Algebra.of F f i)

@[simp]
theorem norm_of (i : I) (x : F i) : ‖of F f hf i x‖ = ‖x‖ := rfl

theorem isometry_of (i : I) : Isometry (of F f hf i) :=
  (AddMonoidHomClass.isometry_iff_norm (of F f hf i)).mpr (norm_of F f hf i)

theorem of_f {i j : I} (h : i ≤ j) (x : F i) :
    of F f hf j (f i j h x) = of F f hf i x := by
  apply (WithAbs.equiv (absoluteValue F f hf)).injective
  exact DirectLimit.Algebra.of_f h x

instance : NormedAlgebra K (Carrier F f hf) where
  norm_smul_le c x := by
    rw [Algebra.smul_def, norm_mul]
    have hc : ‖algebraMap K (Carrier F f hf) c‖ = ‖c‖ := by
      let i : I := Classical.arbitrary I
      change absoluteValue F f hf (algebraMap K (DirectLimit F f) c) = ‖c‖
      rw [DirectLimit.algebraMap_def i]
      exact norm_algebraMap' (F i) c
    rw [hc]

variable [∀ i, IsUltrametricDist (F i)]

theorem absoluteValue_add_le_max (a b : DirectLimit F f) :
    absoluteValue F f hf (a + b) ≤ max (absoluteValue F f hf a) (absoluteValue F f hf b) := by
  induction a, b using DirectLimit.induction₂ f with
  | _ i a b =>
    rw [DirectLimit.add_def]
    exact IsUltrametricDist.norm_add_le_max a b

instance : IsUltrametricDist (Carrier F f hf) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b =>
    absoluteValue_add_le_max F f hf a.ofAbs b.ofAbs

end Langlands.Analytic.IsometricDirectLimit
