import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Representation.Whittaker.GeneralLinear

/-! # Actual local genericity of cuspidal presentations

The local genericity input used at the start of Henniart (2000), Appendix A.2,
for every continuous nontrivial unitary additive character of the local field.
This is a proposition definition, without an existence proof.
-/

noncomputable section

universe uF uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.CompletionPadic

/-- Every irreducible admissible actual local component of every spectral
presentation of a cuspidal realization with unitary central character is
generic for every nontrivial unitary additive character of the canonical
p-adic field, on the original representation and carrier. -/
def CuspidalUnitaryLocalGenericityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
  ∀ (P : CuspidalSpectralPresentation.{uF, uQ} T) (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible),
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
    ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier,
      Whittaker.IsGeneric ψ r
        ((P.localComponent v).padicObject hI hA).obj.representation

end Langlands.Automorphic
