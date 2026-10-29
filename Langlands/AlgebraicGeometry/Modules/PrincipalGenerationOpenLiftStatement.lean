import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.Topology.QuasiSeparated

/-! # Lifting principal opens of a generation open to sections of tensor powers -/

universe u

open AlgebraicGeometry

namespace Langlands.SchemeModule

/-- On a quasi-compact and quasi-separated scheme, for a line bundle `M`, a global section
`s` and a regular function `r` on the whole trivialization open of `s`, some positive
right-associated tensor power of `M` has a global section whose whole trivialization open
is the principal open of `r`. -/
def PrincipalGenerationOpenLiftStatement : Prop :=
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Langlands.AlgebraicGeometry.Picard.LineBundle X)
    (s : Langlands.SchemeModule.GlobalSections M.obj)
    (r : Γ(X, Langlands.SchemeModule.trivializationOpen M.obj s)),
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ t : Langlands.SchemeModule.GlobalSections
        (Langlands.Scheme.Modules.tensorPow M.obj n),
        Langlands.SchemeModule.trivializationOpen
          (Langlands.Scheme.Modules.tensorPow M.obj n) t = X.basicOpen r

end Langlands.SchemeModule
