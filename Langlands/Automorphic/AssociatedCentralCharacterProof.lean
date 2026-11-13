import Langlands.Automorphic.AssociatedCentralCharacterStatement
import Langlands.Automorphic.AssociatedCentralCharacter.DeterminantDescent
import Langlands.Automorphic.AssociatedCentralCharacter.GoodPlaces
import Langlands.Automorphic.AssociatedCentralCharacter.CentralCharacterUniqueness
import Langlands.Automorphic.CentralCharacterTopCoefficient

/-! # Proof of the associated central character statement

Let `S` be weakly associated with the cuspidal realization `T`. The determinant of `S`
descends to a unique Hecke character `δ` (`DeterminantDescent`). At almost every finite
place, `δ` is unramified and its uniformizer value is the top elementary coefficient of the
spectral presentation of `T` (`GoodPlaces`). Hence `T` has central character `δ`
(`CentralCharacterTopCoefficient`), and central characters of `T` are unique
(`CentralCharacterUniqueness`).
-/

noncomputable section

set_option autoImplicit false

universe u uV uP

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global

/-- If a continuous representation of the relative Weil group is weakly associated with a
cuspidal realization, then its determinant descends to a unique Hecke character, which is
the unique central character of the realization. -/
theorem associatedCentralCharacter : AssociatedCentralCharacterStatement.{u, uV, uP} := by
  intro c hc F E _ _ _ _ _ _ _ r S T hassoc
  obtain ⟨P, hP⟩ := (isWeaklyAssociatedClass_isoClass_iff S T).mp hassoc
  obtain ⟨δ, hδ, huniq⟩ := existsUnique_determinantCharacter_eq_reciprocityCharacter hc S hP.1
  have hcent : T.HasCentralCharacter δ :=
    Automorphic.CuspidalOperatorRealization.hasCentralCharacter_of_eventually_elementaryCoefficient
      T P δ (eventually_finiteUniformizerValue_eq_elementaryCoefficient hc hP δ hδ)
  exact ⟨δ, hcent, hδ, fun ω' h' => T.hasCentralCharacter_unique h' hcent, huniq⟩

end Langlands.ClassField.Global.RelativeWeilGroup
