import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionInfinite
import Langlands.GroupScheme.Rational.FiniteFieldCocycleTorusReduction
import Langlands.GroupScheme.Rational.FiniteGaloisFormReductive
import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistence
import Langlands.GroupScheme.CentralIsogeny.StabilizerTorus
import Langlands.GroupScheme.CentralIsogeny.QuasiSplitLift

/-! # Torus reduction for cocycles of quasi-split semisimple groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Steinberg's torus reduction from its remaining prerequisites.** The existence of simply
connected central covers, strongly regular rational points over infinite fields and Steinberg's
rational conjugacy transfer for quasi-split simply connected groups together imply that every
finite-Galois cocycle of a quasi-split semisimple group over a field has an actual torus
reduction. -/
def QuasiSplitCocycleTorusReductionPrerequisitesStatement : Prop :=
  SimplyConnectedCoverExistenceStatement.{u} →
    InfiniteFieldStronglyRegularPointStatement.{u} →
      QuasiSplitSimplyConnectedRegularConjugateStatement.{u} →
        QuasiSplitCocycleTorusReductionStatement.{u}

/-- Finite fields are handled by Lang's theorem; the twist, form, stabilizer-torus and
quasi-split-lift inputs of the infinite case are supplied by their proofs. -/
theorem quasiSplitCocycleTorusReduction_of_prerequisites :
    QuasiSplitCocycleTorusReductionPrerequisitesStatement.{u} := by
  intro hcover hregular hconj K _ G hG hqs L _ _ _ _ ξ
  by_cases hK : Finite K
  · exact Cocycle.nonempty_torusReduction_of_finite hG.isConnectedReductive ξ
  · have : Infinite K := not_finite_iff_infinite.mp hK
    exact quasiSplitCocycleTorusReduction_of_infinite hcover finiteGaloisTwistExistence
      finiteGaloisFormConnectedReductive hregular hconj centralIsogenyStabilizerTorus
      centralIsogenyQuasiSplitLift K G hG hqs L ξ

end Langlands.GroupScheme
