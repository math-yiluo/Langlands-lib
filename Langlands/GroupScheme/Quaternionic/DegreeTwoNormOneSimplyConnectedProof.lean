import Langlands.GroupScheme.Quaternionic.DegreeTwoNormOneSimplyConnectedStatement
import Langlands.GroupScheme.CentralSimpleNormOneSplitting
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.SpecialLinearBinarySymplectic

/-! # Proof: actual degree-two reduced-norm-one groups are simply connected -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.GroupScheme.CentralSimpleUnits

/-- A central simple algebra of dimension four has reduced degree two. -/
theorem reducedDegree_eq_two_of_finrank_eq_four {K A : Type u} [Field K] [Ring A]
    [Algebra K A] (hdim : Module.finrank K A = 4) :
    Langlands.CentralSimple.reducedDegree K A = 2 := by
  rw [Langlands.CentralSimple.reducedDegree, hdim]
  exact Nat.sqrt_eq 2

/-- **Simple connectedness of degree-two norm-one groups.** Over the algebraic closure the
actual reduced-norm-one group becomes `SL_2 = Sp_2`, which is simply connected; simple
connectedness then descends along the algebraic extension. -/
theorem degreeTwoNormOneSimplyConnected : DegreeTwoNormOneSimplyConnectedStatement.{u} := by
  intro K A _ _ _ _ _ _ hdim
  have hSL : ∀ n : ℕ, n = 2 → IsSimplyConnected
      (SpecialLinear.groupScheme (Fin n) (CommRingCat.of (AlgebraicClosure K))) := by
    rintro n rfl
    exact SpecialLinear.BinarySymplectic.isSimplyConnected (AlgebraicClosure K)
  apply IsSimplyConnected.of_algebraicExtension (K := AlgebraicClosure K)
  exact IsSimplyConnected.of_iso
    (Splitting.splittingIso K A (Langlands.CentralSimple.algebraicClosureChart K A))
    (hSL _ (reducedDegree_eq_two_of_finrank_eq_four hdim))

end Langlands.GroupScheme.CentralSimpleUnits
