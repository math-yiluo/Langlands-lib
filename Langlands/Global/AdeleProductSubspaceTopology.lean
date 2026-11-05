import Langlands.Global.AllPlaceSchemePoints

/-! # The product subspace topology on the original adelic ring -/

noncomputable section

universe u

open Topology

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

/-- The literal inclusion of the original curve-place adeles in all completed fields. -/
def curvePlaceCompletionProductMap (a : CurvePlaceAdeleRing k F) :
    ∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v := fun v => a v

theorem curvePlaceCompletionProductMap_injective :
    Function.Injective (curvePlaceCompletionProductMap k F) := by
  intro a b h
  apply RestrictedProduct.ext
  exact congrFun h

/-- Pull back the independent full product topology along the original inclusion. -/
@[instance_reducible]
def curvePlaceProductSubspaceAdeleTopology : TopologicalSpace (CurvePlaceAdeleRing k F) :=
  TopologicalSpace.induced (curvePlaceCompletionProductMap k F) inferInstance

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Every infinite and finite completion, without integrality restrictions. -/
abbrev NumberFieldCompletionProduct :=
  (∀ v : InfinitePlace K, InfiniteCompletion K v) ×
    (∀ v : FinitePlace K, FiniteCompletion K v)

/-- The original full adelic coefficient projections into the unrestricted product. -/
def numberFieldCompletionProductMap (a : Adeles K) : NumberFieldCompletionProduct K :=
  (fun v => infiniteProjection K v a, fun v => finiteProjection K v a)

theorem numberFieldCompletionProductMap_injective :
    Function.Injective (numberFieldCompletionProductMap K) := by
  intro a b h
  apply Prod.ext
  · exact funext (fun v => congrArg (fun z : NumberFieldCompletionProduct K => z.1 v) h)
  · apply RestrictedProduct.ext
    intro v
    exact congrArg (fun z : NumberFieldCompletionProduct K => z.2 v) h

/-- The full product subspace topology, retaining every infinite coefficient. -/
@[instance_reducible]
def numberFieldProductSubspaceAdeleTopology : TopologicalSpace (Adeles K) :=
  TopologicalSpace.induced (numberFieldCompletionProductMap K) inferInstance

end NumberField

end Langlands.Global
