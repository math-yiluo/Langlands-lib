import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Representation.Smooth.Contragredient.Definitions

/-! # Actual cuspidal contragredients and their local components

Three proposition definitions for later proofs: unitary cuspidal dual existence,
existence of a spectral presentation of a supplied dual, and local smooth-dual
compatibility for every pair of presentations. Their derived source provenance
and exact universe conventions are described in the companion Markdown.
-/

noncomputable section

universe uF uP uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.CompletionPadic

/-- An actual cuspidal realization with unitary central character has an actual
full-operator contragredient with unitary central character. -/
def CuspidalUnitaryContragredientExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    ∃ T' : CuspidalOperatorRealization F r,
      T'.realization.IsContragredientOf T.realization ∧
        Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T'

/-- A supplied full-operator dual of a unitary-central-character cusp object has
an actual spectral presentation in any independently specified factor universe,
with irreducible admissible components at every finite place. -/
def CuspidalContragredientPresentationExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T T' : CuspidalOperatorRealization F r),
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    T'.realization.IsContragredientOf T.realization →
  ∀ (_P : CuspidalSpectralPresentation.{uF, uP} T),
    ∃ P' : CuspidalSpectralPresentation.{uF, uQ} T',
      ∀ v : FinitePlace F,
        (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible

/-- Every pair of presentations of actual full-operator dual cusp objects has
contragredient original local actions whenever their actual components are
irreducible and admissible, at every finite place. -/
def CuspidalContragredientLocalCompatibilityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T T' : CuspidalOperatorRealization F r),
    T'.realization.IsContragredientOf T.realization →
  ∀ (P : CuspidalSpectralPresentation.{uF, uP} T)
    (P' : CuspidalSpectralPresentation.{uF, uQ} T') (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible),
    letI := (padicField v).canonicalTopologicalData.topology
    letI : TopologicalSpace (Langlands.GeneralLinear (r.succPNat : ℕ)
      (padicField v).Carrier) := (padicField v).canonicalGeneralLinearTopology _
    letI : IsTopologicalGroup (Langlands.GeneralLinear (r.succPNat : ℕ)
      (padicField v).Carrier) := (padicField v).canonicalGeneralLinearTopologicalGroup _
    let rho := ((P.localComponent v).padicObject hI hA).obj.representation
    let rho' := ((P'.localComponent v).padicObject hI' hA').obj.representation
    Nonempty (rho'.Equiv (Langlands.smoothContragredient rho))

/-- The three actual cuspidal contragredient prerequisites, with independent
field, input-presentation and output-presentation universes. -/
def CuspidalContragredientStatement : Prop :=
  CuspidalUnitaryContragredientExistenceStatement.{uF} ∧
    CuspidalContragredientPresentationExistenceStatement.{uF, uP, uQ} ∧
    CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uQ}

end Langlands.Automorphic
