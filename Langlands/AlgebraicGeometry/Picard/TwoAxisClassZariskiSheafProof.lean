import Langlands.AlgebraicGeometry.Picard.TwoAxisClassFpqcSheaf
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement

/-! # The two-axis class presheaf is a Zariski sheaf (Murre's condition (F1a)) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Murre's condition (F1a) for the two-axis class presheaf: for every abelian scheme `A` over the
spectrum of a noetherian ring, `TwoAxisRigidifiedLineBundle.classPresheaf A` is a sheaf for every
Zariski open cover of every test object. -/
theorem noetherianTwoAxisClassZariskiSheaf : NoetherianTwoAxisClassZariskiSheafStatement.{u} :=
  fun _ _ _ A ↦ UnramifiedFunctor.zariskiSheaf_of_isSheaf_fpqc
    (TwoAxisRigidifiedLineBundle.classPresheaf_isSheaf_fpqc A)

end Langlands.AlgebraicGeometry.Picard
