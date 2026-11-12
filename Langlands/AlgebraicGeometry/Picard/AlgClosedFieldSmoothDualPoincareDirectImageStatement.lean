import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Higher direct images of the Poincaré bundle when the chosen dual is smooth -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `A` be an abelian scheme of relative dimension `g` over an algebraically closed field
`K`, with chosen dual `D = dualScheme A hA` and Poincaré line bundle `P` on `A ×_K D`. If
`D ⟶ Spec K` is smooth of relative dimension `g`, then along the projection `p : A ×_K D ⟶ D`
the higher direct images `Rⁿ p_* P` vanish for `n ≠ g`, and `R^g p_* P` is isomorphic to the
pushforward of the structure sheaf of `Spec K` along the origin of `D`.
This is `AlgClosedFieldPoincareDirectImageStatement` for one `A` whose dual is known to be
smooth of relative dimension `g`.
This definition states a proposition and does not prove it. -/
def AlgClosedFieldSmoothDualPoincareDirectImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ),
    A.HasRelativeDimension g → SmoothOfRelativeDimension g (dualScheme A hA).hom →
      (∀ n : ℕ, n ≠ g →
        IsZero ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom n).obj
          (poincareLineBundle A hA).obj)) ∧
      Nonempty ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom g).obj
          (poincareLineBundle A hA).obj ≅
        (Scheme.Modules.pushforward (dualOrigin A hA).left).obj
          (structureSheaf (Spec (CommRingCat.of K))))

end Langlands.AbelianScheme
