import Langlands.AbelianScheme.IsogenyInverseStatement
import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.Rational

/-! # Conditional rational invertibility for bundled abelian schemes -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

universe u

/-- The precise bundled inverse target, retaining a global kernel annihilator. -/
def IsogenyInverseStatement : Prop :=
  ∀ (S : Scheme.{u}) (A B : AbelianScheme S) (f : A ⟶ B),
    IsIsogeny f →
    (∃ n : ℤ, n ≠ 0 ∧
      GroupScheme.multiplication (GroupScheme.kernel (groupHom f)) n = 1) →
    IsIso ((rationalization S).map f)

/-- The generic inverse target implies the bundled target. -/
theorem isogenyInverseStatement_of_commGroupScheme
    (h : CommGroupScheme.IsogenyInverseStatement.{u}) :
    IsogenyInverseStatement.{u} := by
  intro S A B f hf hn
  have hi := h S A.toCommGroupScheme B.toCommGroupScheme (commHom f) hf hn
  rcases hi.out with ⟨g, hfg, hgf⟩
  exact ⟨g, hfg, hgf⟩

end Langlands.AbelianScheme
