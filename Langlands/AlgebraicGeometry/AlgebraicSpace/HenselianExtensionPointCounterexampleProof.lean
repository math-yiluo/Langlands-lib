import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionPointCounterexampleStatement

/-!
# Conrad's Example 5.13

The Galois-twisted line over `K`, for a separable quadratic extension `K'/K`, is a
quasi-separated algebraic space locally of finite type whose diagonal is an affine immersion,
and the image of its `K`-points in the `K'`-points of its base change is not closed.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open GaloisTwistedLine

/-- **Conrad's Example 5.13.** -/
theorem henselianExtensionPointNotClosed : HenselianExtensionPointNotClosedStatement.{u} := by
  intro K K' _ _ _ _ _ h2 hsep
  have : FiniteDimensional K K' := Module.finite_of_finrank_eq_succ h2
  obtain ⟨D⟩ := QuadraticConj.nonempty h2
  exact ⟨space D, ⟨isQuasiSeparated D, locallyOfFiniteTypeOverBase D⟩, relative_diag D,
    not_isClosed_range D⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
