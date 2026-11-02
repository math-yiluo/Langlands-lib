import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Ultrametric completion of a seminormed additive group -/

namespace Langlands.Analytic

/-- The metric completion of an ultrametric seminormed group is ultrametric. -/
instance completion_isUltrametricDist {E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] : IsUltrametricDist (UniformSpace.Completion E) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    UniformSpace.Completion.induction_on₂ x y
      (isClosed_le (continuous_norm.comp continuous_add)
        ((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)))
      fun a b => by
        rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
          UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
        exact IsUltrametricDist.norm_add_le_max a b

end Langlands.Analytic
