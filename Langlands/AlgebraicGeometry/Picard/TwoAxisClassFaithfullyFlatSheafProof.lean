import Langlands.AlgebraicGeometry.Picard.TwoAxisClassFpqcSheaf
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement

/-! # The two-axis class presheaf satisfies fpqc descent (Murre's condition (F1b)) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Murre's condition (F1b) for the two-axis class presheaf: for every abelian scheme `A` over the
spectrum of a noetherian ring, `TwoAxisRigidifiedLineBundle.classPresheaf A` satisfies the sheaf
condition for every faithfully flat quasi-compact morphism of test objects. -/
theorem noetherianTwoAxisClassFaithfullyFlatSheaf :
    NoetherianTwoAxisClassFaithfullyFlatSheafStatement.{u} :=
  fun _ _ _ A ↦ UnramifiedFunctor.faithfullyFlatSheaf_of_isSheaf_fpqc
    (TwoAxisRigidifiedLineBundle.classPresheaf_isSheaf_fpqc A)

end Langlands.AlgebraicGeometry.Picard
