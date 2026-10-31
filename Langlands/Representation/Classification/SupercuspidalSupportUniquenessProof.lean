import Langlands.Representation.Classification.SupercuspidalSupportStatement
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.CuspidalSupport.AssociationReverseProof

/-! Uniqueness of supercuspidal support from reverse cuspidal-induction association. -/

namespace Langlands

open CuspidalSupport PadicField.TopologicalData

universe uV uF

/-- Any two supercuspidal supports of an irreducible smooth representation
of `GL_n(F)` are equal, with independent field and factor universes. -/
theorem glSupercuspidalSupportUniqueness :
    GLSupercuspidalSupportUniquenessStatement.{uV, uF} := by
  intro p _ F T n hn
  let := T.topology
  intro π hπ s s' hs hs'
  obtain ⟨k, ρ, hρ, h, A, hA, _, hsub⟩ := hs
  obtain ⟨l, ρ', hρ', h', A', hA', _, hsub'⟩ := hs'
  have hσ := glCuspidalTensor.{uV, uF} p F T n hn (T.cuspidalShape ρ h) A
  have hτ := glCuspidalTensor.{uV, uF} p F T n hn (T.cuspidalShape ρ' h') A'
  have hassoc := cuspidalInductionReverseAssociation.{uF, uV, uV} p F T n
    (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h')
    (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
    (FiniteTensor.externalSmoothObject (fun i => (A' i).obj))
    hσ.1 hσ.2 hτ.1 hτ.2
  apply hρ.symm.trans
  apply Eq.trans _ hρ'
  apply glCuspidalTensorAssociation.{uV, uF} p F T n hn
    k l ρ ρ' h h' A A' hA hA'
  apply hassoc
  obtain ⟨S, Q, ⟨e⟩⟩ := hsub
  obtain ⟨S', Q', ⟨e'⟩⟩ := hsub'
  refine ⟨S, Q, S', Q', ?_, ⟨SmoothRep.equivOfIso (e.symm.trans e')⟩⟩
  exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e)).mp hπ

end Langlands
