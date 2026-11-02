import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Higher direct images of the Poincaré bundle over an algebraically closed field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `A` be an abelian scheme of relative dimension `g` over an algebraically closed field
`K`, with chosen dual `D = dualScheme A hA` and Poincaré line bundle `P` on `A ×_K D`. Along the
projection `p : A ×_K D ⟶ D`, the higher direct images `Rⁿ p_* P` vanish for `n ≠ g`, and
`R^g p_* P` is isomorphic to the pushforward of the structure sheaf of `Spec K` along the
origin of `D`, the skyscraper sheaf with stalk `K` at the origin.
This definition states a proposition and does not prove it. -/
def AlgClosedFieldPoincareDirectImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ),
    A.HasRelativeDimension g →
      (∀ n : ℕ, n ≠ g →
        IsZero ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom n).obj
          (poincareLineBundle A hA).obj)) ∧
      Nonempty ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom g).obj
          (poincareLineBundle A hA).obj ≅
        (Scheme.Modules.pushforward (dualOrigin A hA).left).obj
          (structureSheaf (Spec (CommRingCat.of K))))

end Langlands.AbelianScheme
