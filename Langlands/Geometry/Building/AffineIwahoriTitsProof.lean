import Langlands.Geometry.Building.AffineIwahoriTitsStatement
import Langlands.Geometry.Building.AffineIwahoriTitsNormalizerReduction
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingProof
import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationProof
import Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsProof

/-! # The apartment-only affine Iwahori–Tits statement: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **The affine Iwahori–Tits system** (Kaletha–Prasad, Theorem 7.5.3(1),(2), the `G(F)^0`
branch). For parahoric building data satisfying the apartment axioms and every chamber of the
apartment, `N(F) ∩ G(F)^0` and `G(F)^0` are normal and the actual `G(F)^0` Iwahori–Tits system
exists. -/
theorem affineIwahoriTits : AffineIwahoriTitsStatement.{u} :=
  affineIwahoriTitsStatement_of_localArithmeticInputs
    Langlands.GroupScheme.localSimplyConnectedCocycleVanishing
    Langlands.GroupScheme.localRankOneClassification
    Langlands.GroupScheme.Quaternionic.localSpinKneserTits

end Langlands.Geometry.Building
