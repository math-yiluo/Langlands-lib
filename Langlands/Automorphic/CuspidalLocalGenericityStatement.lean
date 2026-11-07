import Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement

/-! # Actual local genericity of all cuspidal presentations

The local genericity of every irreducible admissible finite-place component
of every spectral presentation of an actual cuspidal operator realization,
for every continuous nontrivial unitary additive character of the local field.
Unlike `CuspidalUnitaryLocalGenericityStatement`, no unitary central character
is assumed. This is a proposition definition, without an existence proof.
-/

noncomputable section

universe uF uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.CompletionPadic

/-- Every irreducible admissible actual local component of every spectral
presentation of a cuspidal realization is generic for every nontrivial unitary
additive character of the canonical p-adic field, on the original
representation and carrier. No central-character hypothesis is imposed. -/
def CuspidalLocalGenericityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uQ} T) (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible),
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
    ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier,
      Whittaker.IsGeneric ψ r
        ((P.localComponent v).padicObject hI hA).obj.representation

/-- The unrestricted statement specializes to the unitary-central-character
statement by ignoring its extra premise. -/
theorem CuspidalLocalGenericityStatement.toUnitary
    (h : CuspidalLocalGenericityStatement.{uF, uQ}) :
    CuspidalUnitaryLocalGenericityStatement.{uF, uQ} :=
  fun F _ _ _ r T _ P v hI hA ψ => h F r T P v hI hA ψ

end Langlands.Automorphic
