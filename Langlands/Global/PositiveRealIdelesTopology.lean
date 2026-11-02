import Langlands.Global.PositiveRealIdeles

/-!
# Closedness of the actual positive scalar idele subgroup

The unweighted norm at any one infinite place is a continuous retraction of
the scalar map. Thus that map is a closed topological embedding.
-/

noncomputable section

universe u v

namespace Langlands.Global.PositiveRealIdeles

open Topology
open scoped NNReal RestrictedProduct

variable (F : Type u) [Field F] [NumberField F]

/-- The unweighted local norm on units of an archimedean completion. -/
def localNorm (w : InfinitePlace F) : (InfiniteCompletion F w)ˣ →ₜ* ℝ≥0ˣ where
  toMonoidHom := Units.map
    (nnnormHom : InfiniteCompletion F w →*₀ ℝ≥0).toMonoidHom
  continuous_toFun := continuous_nnnorm.units_map _

/-- The norm at a single infinite place, as a continuous homomorphism on ideles. -/
def normRetraction (w : InfinitePlace F) : Ideles F →ₜ* ℝ≥0ˣ :=
  (localNorm F w).comp (infiniteIdeleProjection F w)

@[simp]
theorem coe_normRetraction (w : InfinitePlace F) (g : Ideles F) :
    ((normRetraction F w g : ℝ≥0) : ℝ) = ‖g.val.1 w‖ := rfl

@[simp]
theorem normRetraction_full (w : InfinitePlace F) (x : ℝ≥0ˣ) :
    normRetraction F w (full F x) = x := by
  apply Units.ext
  apply NNReal.eq
  exact norm_full_infinite_value F w x

theorem normRetraction_leftInverse (w : InfinitePlace F) :
    Function.LeftInverse (normRetraction F w) (full F) :=
  normRetraction_full F w

/-- The scalar map is a closed embedding in the actual units topology of the ideles. -/
theorem isClosedEmbedding_full : IsClosedEmbedding (full F) := by
  classical
  let : T2Space (InfiniteAdeles F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeles F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (Adeles F) :=
    inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))
  let w : InfinitePlace F := Classical.arbitrary _
  exact (normRetraction_leftInverse F w).isClosedEmbedding
    (normRetraction F w).continuous (full F).continuous

theorem isClosed_range_full : IsClosed (Set.range (full F)) :=
  (isClosedEmbedding_full F).isClosed_range

/-- A family of scalar idele maps is again a closed embedding, including empty families. -/
theorem isClosedEmbedding_full_pi (I : Type v) :
    IsClosedEmbedding (fun x : I → ℝ≥0ˣ => fun i => full F (x i)) :=
  Topology.IsClosedEmbedding.piMap fun _ => isClosedEmbedding_full F

end Langlands.Global.PositiveRealIdeles
