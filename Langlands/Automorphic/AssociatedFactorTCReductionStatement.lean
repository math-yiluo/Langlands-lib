import Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement
import Langlands.Automorphic.AssociatedFactorTCStatement

/-!
# Reductions between the totally complex forms of the cuspidal-pair and associated-factor
statements

Three implications between totally complex forms, each the totally complex form of a link of
the Library's route:

* `Langlands.Global.CuspidalPairFunctionalEquationReductionTCStatement`: the local data of
  cuspidal pairs, the totally complex archimedean parameters and the totally complex completed
  equation imply the totally complex global functional equation (the totally complex form of
  `CuspidalPairFunctionalEquationReductionStatement`);
* `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedGammaReductionTCStatement`: the
  totally complex global functional equation implies the totally complex form of Henniart's
  Théorème 2.3 (the totally complex form of the published `associatedGamma_of_inputs`, whose
  second input `StableTwistPairGammaMatchStatement` is proved);
* `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement`:
  the totally complex forms of Théorème 2.4 and Corollaire 2.3 imply that of Corollaire 2.4
  (the totally complex form of `AssociatedCuspidalFactorReductionStatement`).

Proposition definitions only.
-/

noncomputable section

universe u uV uP uQ uE

namespace Langlands.Global

/-- The local data of cuspidal pairs, the existence of archimedean parameters of cuspidal
realizations over totally complex fields and the completed equation over totally complex
fields together imply the completed Rankin–Selberg functional equation of cuspidal pairs over
totally complex fields. -/
def CuspidalPairFunctionalEquationReductionTCStatement : Prop :=
  CuspidalPairLocalDataStatement.{u, uQ} →
    CuspidalArchimedeanParameterExistenceTCStatement.{u} →
      CuspidalPairCompletedEquationTCStatement.{u, uQ} →
        CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ}

end Langlands.Global

namespace Langlands.ClassField.Global.RelativeWeilGroup

/-- The completed global Rankin–Selberg functional equation of cuspidal pairs over totally
complex fields implies Henniart's Théorème 2.3 over totally complex fields. -/
def AssociatedGammaReductionTCStatement : Prop :=
  Langlands.Global.CuspidalPairGlobalFunctionalEquationTCStatement.{u, u} →
    AssociatedGammaTCStatement.{u, uV, uP, uQ, uE}

/-- Henniart's Théorème 2.4 and Corollaire 2.3 over totally complex fields imply his
Corollaire 2.4 over totally complex fields, at five independent universe levels. -/
def AssociatedCuspidalFactorReductionTCStatement : Prop :=
  AssociatedSupercuspidalInductionTCStatement.{u, uV, uP, uQ} →
    AssociatedTemperedFactorTCStatement.{u, uV, uP, uQ, uE} →
      AssociatedCuspidalFactorTCStatement.{u, uV, uP, uQ, uE}

end Langlands.ClassField.Global.RelativeWeilGroup
