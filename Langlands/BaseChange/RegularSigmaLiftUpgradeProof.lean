import Langlands.BaseChange.RegularSigmaLiftUpgradeStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentity.RegularForward

/-!
# Proof that the regular σ-lift identity implies the σ-lift identity

The regular identity gives the Shintani identity
(`SigmaLiftCharacterIdentity.isShintaniLift_of_isRegularSigmaLift`), and the Shintani identity
gives the σ-lift identity (`sigmaLiftCharacterIdentityReverse`). See Henniart–Lemaire (2011),
II.2.9 and II.6.13, and Arthur–Clozel (1989), Chapter 1, §6.3.
-/

namespace Langlands.BaseChange

universe u v uV uW

/-- Under the eight premises of `RegularSigmaLiftUpgradeStatement`, the regular σ-lift
identity implies the σ-lift identity for the same intertwiner and constant. -/
theorem regularSigmaLiftUpgrade : RegularSigmaLiftUpgradeStatement.{u, v, uV, uW} := by
  intro hregularF hregularE htransfer hintegrals hopen hIntegral hOrdinary hTwisted
    F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ τ hτ hπirr hτirr A c hreg
  exact sigmaLiftCharacterIdentityReverse hIntegral hOrdinary hTwisted F E σ l n hE
    π hπ τ hτ hπirr hτirr A c
    (SigmaLiftCharacterIdentity.isShintaniLift_of_isRegularSigmaLift hregularF hregularE
      htransfer hintegrals hopen F E σ l n hE π hπ τ hτ hπirr hτirr A c hreg)

end Langlands.BaseChange
