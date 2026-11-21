import Langlands.Automorphic.HeckeDeterminantTwistDualitySupercuspidalStatement
import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Correspondence.SupercuspidalOperationRealization

/-! # Supercuspidality under an actual Hecke determinant twist -/

universe uE uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Correspondence

/-- A Hecke determinant twist preserves supercuspidality at the given finite place. -/
theorem heckeDeterminantTwistSupercuspidal :
    HeckeDeterminantTwistSupercuspidalStatement.{uE, uV} := by
  intro E _ _ _ r S P ν v h
  obtain ⟨hI, hA, σ, hσ⟩ := h
  have hI' := (P.heckeDeterminantTwist_localComponent_isIrreducible_iff ν v).mpr hI
  have hA' := (P.heckeDeterminantTwist_localComponent_isAdmissible_iff ν v).mpr hA
  let K := CompletionPadic.padicField v
  let χ := CompletionPadic.quasicharacterBase v (ν.finiteComponent v)
  have htw := P.isCharacterTwist_heckeDeterminantTwist_padicClass ν v hI hA hI' hA'
  have heq := (isCharacterTwist_iff_eq_twist K χ
    (isOpen_ker_determinantQuasiCharacter K r.succPNat χ) _ _).mp htw
  refine ⟨hI', hA', supercuspidalTwist K χ σ, ?_⟩
  rw [heq, ← hσ]
  let : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
  exact GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist
    (determinantQuasiCharacter K r.succPNat χ) _ _ σ

end Langlands.Automorphic
