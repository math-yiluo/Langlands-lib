import Langlands.CommutativeAlgebra.AlgClosedResidueDvrExtension
import Langlands.CommutativeAlgebra.DvrCompletion

/-! # Complete DVR base extensions with algebraically closed residue field -/

noncomputable section

universe u

open IsLocalRing

namespace Langlands.CommutativeAlgebra

/-- A DVR admits a same-universe faithfully flat DVR extension that is complete in
its maximal-ideal adic topology and has algebraically closed residue field. -/
theorem exists_completeAlgClosedResidueDvrExtension (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S), Module.FaithfullyFlat R S ∧
        IsAdicComplete (maximalIdeal S) S ∧ IsAlgClosed (ResidueField S) := by
  obtain ⟨S, _, _, _, _, hFlat, hClosed⟩ := exists_algClosedResidueDvrExtension R
  let T := AdicCompletion (maximalIdeal S) S
  obtain ⟨hDomain, hDvr⟩ := DvrCompletion.isDomain_and_isDiscreteValuationRing S
  have : Module.FaithfullyFlat S T := DvrCompletion.faithfullyFlat S
  have hClosedT : IsAlgClosed (ResidueField T) :=
    IsAlgClosed.of_ringEquiv (ResidueField S) (ResidueField T) (DvrCompletion.residueEquiv S)
  exact ⟨T, inferInstance, hDomain, hDvr, inferInstance, Module.FaithfullyFlat.trans R S T,
    inferInstance, hClosedT⟩

end Langlands.CommutativeAlgebra
