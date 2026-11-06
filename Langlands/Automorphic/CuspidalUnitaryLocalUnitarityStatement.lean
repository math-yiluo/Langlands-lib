import Langlands.Automorphic.AssociatedFactorStatement

/-! # Actual local unitarity of cuspidal presentations

The local unitarity input used at the start of Henniart (2000), Appendix A.2.
This is a proposition definition, without an existence proof.
-/

noncomputable section

universe uF uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.CompletionPadic

/-- Every irreducible admissible actual local component of every spectral
presentation of a cuspidal realization with unitary central character admits
an invariant positive definite Hermitian form on its original carrier. -/
def CuspidalUnitaryLocalUnitarityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
  ∀ (P : CuspidalSpectralPresentation.{uF, uQ} T) (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible),
    letI := (padicField v).canonicalTopologicalData.topology
    IsUnitarizable ((P.localComponent v).padicObject hI hA).obj.representation

end Langlands.Automorphic
