import Langlands.Global.FunctionFieldAbsoluteValueCompletions
import Langlands.Global.CurvePlaceAdeleRing
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Langlands.Global.Adelic
import Mathlib.Topology.NhdsWithin

/-! # Weak approximation in the original global-field completions -/

noncomputable section

universe u

open Topology

namespace Langlands.Global

section FunctionField

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

private def curveCompletionCast {v w : AlgebraicCurve.Place k F} (h : v = w) :
    curvePlaceCompletion v ≃+* curvePlaceCompletion w where
  toFun x := h ▸ x
  invFun x := h.symm ▸ x
  left_inv x := by subst w; rfl
  right_inv x := by subst w; rfl
  map_mul' x y := by subst w; rfl
  map_add' x y := by subst w; rfl

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem continuous_curveCompletionCast {v w : AlgebraicCurve.Place k F}
    (h : v = w) : Continuous (curveCompletionCast k F h) := by
  subst w
  exact continuous_id

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem curveCompletionCast_algebraMap {v w : AlgebraicCurve.Place k F}
    (h : v = w) (x : F) :
    curveCompletionCast k F h (algebraMap F (curvePlaceCompletion v) x) =
      algebraMap F (curvePlaceCompletion w) x := by
  subst w
  rfl

/-- The chosen real absolute value of an actual curve place has the original
adic completion, by the published comparison and its exact place identity. -/
def curvePlaceRealCompletionEquiv (v : AlgebraicCurve.Place k F) :
    (curvePlaceRealAbsoluteValue k F v).val.Completion ≃+* curvePlaceCompletion v :=
  (functionFieldAbsoluteValueCompletionEquiv k F (curvePlaceRealAbsoluteValue k F v)).trans
    (curveCompletionCast k F
      (functionFieldPlaceOfAbsoluteValue_curvePlaceRealAbsoluteValue k F v))

theorem continuous_curvePlaceRealCompletionEquiv (v : AlgebraicCurve.Place k F) :
    Continuous (curvePlaceRealCompletionEquiv k F v) :=
  (continuous_curveCompletionCast k F _).comp
    (continuous_functionFieldAbsoluteValueCompletionEquiv k F
      (curvePlaceRealAbsoluteValue k F v))

theorem curvePlaceRealCompletionEquiv_coe (v : AlgebraicCurve.Place k F) (x : F) :
    curvePlaceRealCompletionEquiv k F v
      ((WithAbs.toAbs (curvePlaceRealAbsoluteValue k F v).val x :
        WithAbs (curvePlaceRealAbsoluteValue k F v).val) : _) =
      algebraMap F (curvePlaceCompletion v) x := by
  change curveCompletionCast k F _
    (functionFieldAbsoluteValueCompletionEquiv k F
      (curvePlaceRealAbsoluteValue k F v) _) = _
  rw [functionFieldAbsoluteValueCompletionEquiv_coe, curveCompletionCast_algebraMap]

/-- The original field with the chosen absolute-value topology embeds densely
and continuously in its actual curve-place completion. -/
def curvePlaceWithAbsEmbedding (v : AlgebraicCurve.Place k F) :
    WithAbs (curvePlaceRealAbsoluteValue k F v).val → curvePlaceCompletion v :=
  fun x => curvePlaceRealCompletionEquiv k F v x

theorem continuous_curvePlaceWithAbsEmbedding (v : AlgebraicCurve.Place k F) :
    Continuous (curvePlaceWithAbsEmbedding k F v) :=
  (continuous_curvePlaceRealCompletionEquiv k F v).comp
    (UniformSpace.Completion.continuous_coe _)

theorem denseRange_curvePlaceWithAbsEmbedding (v : AlgebraicCurve.Place k F) :
    DenseRange (curvePlaceWithAbsEmbedding k F v) :=
  (curvePlaceRealCompletionEquiv k F v).surjective.denseRange.comp
    UniformSpace.Completion.denseRange_coe
    (continuous_curvePlaceRealCompletionEquiv k F v)

@[simp]
theorem curvePlaceWithAbsEmbedding_toAbs (v : AlgebraicCurve.Place k F) (x : F) :
    curvePlaceWithAbsEmbedding k F v
      (WithAbs.toAbs (curvePlaceRealAbsoluteValue k F v).val x) =
      algebraMap F (curvePlaceCompletion v) x :=
  curvePlaceRealCompletionEquiv_coe k F v x

/-- The actual diagonal into any finite family of original curve-place completions. -/
def curvePlaceFiniteCompletionDiagonal (S : Finset (AlgebraicCurve.Place k F)) :
    F →+* (∀ v : S, curvePlaceCompletion v.val) :=
  algebraMap F _

theorem curvePlaceRealAbsoluteValue_pairwise_not_isEquiv
    (S : Finset (AlgebraicCurve.Place k F)) :
    Pairwise (fun v w : S =>
      ¬ (curvePlaceRealAbsoluteValue k F v.val).val.IsEquiv
        (curvePlaceRealAbsoluteValue k F w.val).val) := by
  intro v w hvw h
  apply hvw
  apply Subtype.ext
  have he := (functionFieldPlaceOfAbsoluteValue_eq_iff k F _ _).mpr h
  simpa only [functionFieldPlaceOfAbsoluteValue_curvePlaceRealAbsoluteValue] using he

/-- Weak approximation in the actual finite product, with no separability premise. -/
theorem denseRange_curvePlaceFiniteCompletionDiagonal
    (S : Finset (AlgebraicCurve.Place k F)) :
    DenseRange (curvePlaceFiniteCompletionDiagonal k F S) := by
  let a : S → AbsoluteValue F ℝ := fun v => (curvePlaceRealAbsoluteValue k F v.val).val
  have hd : DenseRange (algebraMap F (∀ v : S, WithAbs (a v))) :=
    AbsoluteValue.denseRange_algebraMap_pi
      (fun v => (curvePlaceRealAbsoluteValue k F v.val).property)
      (curvePlaceRealAbsoluteValue_pairwise_not_isEquiv k F S)
  have he : DenseRange (Pi.map (fun v : S => curvePlaceWithAbsEmbedding k F v.val)) :=
    DenseRange.piMap (fun v => denseRange_curvePlaceWithAbsEmbedding k F v.val)
  have hc : Continuous (Pi.map (fun v : S => curvePlaceWithAbsEmbedding k F v.val)) :=
    Continuous.piMap (fun v => continuous_curvePlaceWithAbsEmbedding k F v.val)
  convert he.comp hd hc using 1
  funext x v
  exact (curvePlaceWithAbsEmbedding_toAbs k F v.val x).symm

end FunctionField

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- The actual mixed diagonal keeps all infinite completions and any finite
family of finite completions. -/
def numberFieldFiniteCompletionDiagonal (S : Finset (FinitePlace K)) :
    K →+* ((∀ v : InfinitePlace K, InfiniteCompletion K v) ×
      (∀ v : S, FiniteCompletion K v.val)) :=
  algebraMap K _

theorem denseRange_numberFieldFiniteCompletionDiagonal (S : Finset (FinitePlace K)) :
    DenseRange (numberFieldFiniteCompletionDiagonal K S) := by
  intro z
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hU
  rw [nhds_pi] at hV hW
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.mp hV
  obtain ⟨J, s, hs, hJs⟩ := Filter.mem_pi'.mp hW
  obtain ⟨x, hxf, hxi⟩ := AdelicFunctoriality.exists_algebraMap_mem_open S
    (fun v => interior (s v)) (fun _ => isOpen_interior)
    (fun v => ⟨z.2 v, mem_interior_iff_mem_nhds.mpr (hs v)⟩)
    (fun v => interior (t v)) (fun _ => isOpen_interior)
    (fun v => ⟨z.1 v, mem_interior_iff_mem_nhds.mpr (ht v)⟩)
  refine ⟨numberFieldFiniteCompletionDiagonal K S x, hVW ?_, ⟨x, rfl⟩⟩
  exact ⟨hIt (fun v _ => interior_subset (hxi v)),
    hJs (fun v _ => interior_subset (hxf v))⟩

end NumberField

end Langlands.Global
