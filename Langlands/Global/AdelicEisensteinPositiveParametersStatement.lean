import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.PositiveRealTorusIntrinsic

/-! # Logarithms and complex parameters of the positive Levi split component -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- On the actual positive split component of a compatible parabolic
presentation, the logarithm attains every real character functional, and
the restricted powers distinguish complex parabolic parameters. -/
def EisensteinPositiveParametersStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (_r : ParabolicRootPresentation p l a),
    let S := PositiveRealTorus.imageSubgroup F A P (a ≫ l)
    Function.Surjective (fun x : S => characterLog F P x.val) ∧
      Function.Injective (fun lam : ComplexCharacterParameter F P =>
        fun x : S => parameterPower F P lam x.val)

end Langlands.Global
