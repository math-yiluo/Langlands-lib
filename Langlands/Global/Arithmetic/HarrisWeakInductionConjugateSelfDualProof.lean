import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof
import Langlands.Automorphic.ConjugateSelfDualCriterion
import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.WeakAutomorphicInductionArithmeticTransport
import Langlands.Automorphic.Unramified.ContragredientWeakInduction

/-!
# Conjugate self-duality of a weak automorphic induction of a conjugate-inverse character

The proof of `WeakInductionConjugateInverseSelfDualStatement`, through a core result that
takes Euler constituent recovery at the base field as its only rigidity input; the module
`HarrisWeakInductionConjugateSelfDualTCProof` applies the same core to the totally complex
rigidity premise.

Let `E ⊆ E'` be CM fields, `ξ` a Hecke character of `E'` with `ξ ∘ c = ξ⁻¹`, and `S` a
cuspidal realization over `E` that is a weak automorphic induction of `ξ`. Take a
realization `Sd` of the contragredient of `S`. It is a weak induction of `ξ⁻¹`; its pullback
along the CM involution of `E`, which is its CM image `Sd.complexConj`, is then a weak
induction of the pullback of `ξ⁻¹` along the CM involution of `E'`, which is `ξ`. Two weak
inductions of `ξ` have the same Euler polynomials at almost all places, so Euler constituent
recovery over `E` identifies `Sd.complexConj` with `S`, and the contragredient pairing of
`S.complexConj` gives the conjugate-contragredient pairing of `S`.
-/

noncomputable section

universe uV uE uE'

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Unramified
open Langlands.Global.CMConjugation

/-- The common core of both statements. Over a CM field `E`, given Euler constituent
recovery at `E` (the third component of the rigidity premise at the field `E`), a cuspidal
class that is a weak automorphic induction of a conjugate-inverse Hecke character of a CM
extension `E'` is conjugate self-dual. -/
theorem isConjugateSelfDual_of_isWeakAutomorphicInductionOf_of_isConjugateInverse
    {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [IsCMField E]
    [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E'] [CompactSpace (AdeleQuotient E)]
    (hRig : ∀ (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass E)
      (d : Fin q → PositiveRankCuspidalClass E)
      (s : ∀ i, SpectralSystem (FinitePlace E) (c i).rank)
      (t : ∀ j, SpectralSystem (FinitePlace E) (d j).rank),
      (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uE, uV} (c i) (s i)) →
      (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uE, uV} (d j) (t j)) →
      (SpectralSystem.finiteSum s).SameEulerPolynomials (SpectralSystem.finiteSum t) →
      ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i))
    {ξ : HeckeCharacter E'} (hξ : IsConjugateInverse ξ) {r : ℕ}
    {c : CuspidalOperatorRealization.IsoClass E r}
    (hc : c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ) : c.IsConjugateSelfDual := by
  obtain ⟨S, rfl⟩ := c.exists_representative
  obtain ⟨Sd, hSd⟩ := cuspidalContragredientExistence E r S
  -- The contragredient is a weak induction of `ξ⁻¹`.
  have hinv :=
    CuspidalOperatorRealization.IsoClass.isWeakAutomorphicInductionOf_inv_of_isContragredientOf
      S Sd hSd hc
  -- Pull back along the CM involutions of `E` and `E'`, which commute with `E → E'`.
  have hconj := hinv.arithmeticComap (fieldConj E) (fieldConj E')
    (fun x => HarrisDatum.complexConj_algebraMap x)
  have hξ' : HeckeCharacter.comap (fieldConj E') ξ⁻¹ = ξ := by
    have h : HeckeCharacter.comap (fieldConj E') ξ = ξ⁻¹ := DFunLike.ext _ _ fun x => hξ x
    rw [HeckeCharacter.comap_inv, h]
    exact DFunLike.ext _ _ fun x => inv_inv (ξ x)
  rw [hξ', CuspidalOperatorRealization.IsoClass.arithmeticComap_fieldConj,
    CuspidalOperatorRealization.IsoClass.complexConj_isoClass] at hconj
  -- Compare the two weak inductions of `ξ` by Euler constituent recovery.
  obtain ⟨s, hs, hsξ⟩ := hc
  obtain ⟨t, ht, htξ⟩ := hconj
  exact CuspidalOperatorRealization.isoClass_isConjugateSelfDual_of_isContragredientOf S Sd hSd
    (CuspidalOperatorRealization.IsoClass.eq_of_sameEulerPolynomials hRig ht hs
      (htξ.sameEulerPolynomials hsξ))

/-- `WeakInductionConjugateInverseSelfDualStatement`: given spectral rigidity, a weak
automorphic induction over a CM field `E` of a conjugate-inverse Hecke character of a CM
extension `E'` is conjugate self-dual. -/
theorem weakInductionConjugateInverseSelfDual :
    WeakInductionConjugateInverseSelfDualStatement.{uV, uE, uE'} := by
  intro hRig E E' _ _ _ _ _ _ _ _ ξ r c hξ hc
  exact isConjugateSelfDual_of_isWeakAutomorphicInductionOf_of_isConjugateInverse
    (hRig.2.2 E) hξ hc

end Langlands.Global.Harris
