import Langlands.Representation.CuspidalSupport.AssociationForwardStatement
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport
import Langlands.Representation.CuspidalSupport.BlockWeylTransport
import Langlands.Representation.CuspidalSupport.ConstituentProof
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-! Proof of BZ77 Theorem 2.9(a), (i) ⇒ (ii): associated irreducible cuspidal
inducing data have a nonzero intertwiner between their normalized inductions. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV uW

/-- BZ77 Theorem 2.9(a), (i) ⇒ (ii): associated irreducible cuspidal inducing
data have a nonzero intertwiner between their normalized inductions. -/
theorem associatedCuspidalInductionHomTheorem :
    AssociatedCuspidalInductionHomTheorem.{uF, uV, uW} := by
  intro p _ F T n _
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ _ hσc hτ hτc hassoc
  obtain ⟨v, ⟨ev⟩⟩ := exists_minimal_transport_equiv_of_associated B C hassoc
  have hlev : LevisAssociated (F := F.Carrier) B C := ⟨⟨v.val.val, v.property⟩⟩
  obtain ⟨_, r, e, s, hs⟩ :=
    associatedJacquetFiltration.{uF, uV} F T n B C σ hσc.2 hlev
  let := T.valuativeRel
  let := T.localField
  have hA : ((T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj σ)).IsAdmissible :=
    isAdmissible_of_transportFiltration B C s (SmoothRep.isSmooth _)
      (fun i => ⟨(e i).val.val, (e i).property⟩) hσc.1 hs
  have htr : ∀ u u' : MinimalConjugatingPermutations (F := F.Carrier) B C, u = u' →
      (transport B C u.val.val u.property σ.representation).Equiv
        (transport B C u'.val.val u'.property σ.representation) := by
    rintro u _ rfl
    exact Representation.Equiv.refl _
  obtain ⟨g⟩ := hs (e.symm v)
  exact exists_ne_zero_of_gradedRepresentation_equiv T B C
    (leviCuspidalConstituentTheorem.{uF, max uF uV} F T C) σ τ hτ hτc
    hA r s (e.symm v) ⟨(g.trans (htr _ _ (e.apply_symm_apply v))).trans ev⟩

end Langlands.CuspidalSupport
