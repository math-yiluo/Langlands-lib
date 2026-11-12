import Langlands.Global.Adelic
import Langlands.Global.CurvePlaceAdeleRing
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.NumberTheory.FunctionField

/-!
# Adele rings are not noetherian

Conrad, printed p.5: finite presentation coincides with finite type over a noetherian ring,
"but the adele ring `A_F` is not noetherian".
-/

universe u

namespace Langlands.Global

/-- Conrad's remark (printed p.5) that adele rings are not noetherian, for the actual adele
ring of every number field and the actual curve-place adele ring of every function field over
an arbitrary constant field. -/
def AdeleRingNotNoetherianStatement : Prop :=
  (∀ (K : Type u) [Field K] [NumberField K], ¬ IsNoetherianRing (Adeles K)) ∧
    ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
      [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
      ¬ IsNoetherianRing (CurvePlaceAdeleRing k F)

end Langlands.Global
