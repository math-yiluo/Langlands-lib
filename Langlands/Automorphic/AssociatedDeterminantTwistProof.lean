import Langlands.Automorphic.AssociatedDeterminantTwistStatement
import Langlands.Automorphic.AssociatedCentralCharacterProof
import Langlands.Automorphic.AssociatedPresentationSpectrum
import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.HeckeDeterminantTwistAssociationProof

/-! # Determinants and finite-order twists under weak association

Proof of `AssociatedDeterminantTwistStatement`, Henniart (2000), §2.2, for representations of
the relative Weil group of an arithmetic class family and cuspidal realizations of `GL_{r+1}`.

* Determinant: the supplied presentation witnesses class-level association, so
  `associatedCentralCharacter` gives a central character `δ` of `T` with
  `det S = δ ∘ τ_F`, and the uniqueness of central characters identifies `δ` with the
  supplied `ω`.
* Presented twist: `presentedDeterminantMultipleAssociation` applies to the constructed
  finite-order twist `T.determinantTwist χ` and its twisted presentation. That realization is
  equivalent to the given twist `T'` (`IsFiniteOrderDeterminantTwist.target_equivalent`), so
  the association is a class-level witness for `T'`, and `IsWeaklyAssociatedClass.presentation`
  transfers it to the given presentation `P'`.
* Class twist: on representatives, an irreducible admissible finite slice of `T'`
  (`cuspidalIrreducibleAdmissibleFiniteSliceExistence`), Flath's factorization
  (`exists_presentation_of_finiteSlice`) and the small-realization comparison
  (`CuspidalSpectralPresentation.exists_small`) give a presentation of `T'` in the requested
  factor universe, to which the presented twist applies.
-/

set_option autoImplicit false

universe u uV uP uQ

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global

/-- Under weak association the determinant equals the pullback of the supplied central
character by inverse transfer. -/
theorem presentedDeterminantAssociation : PresentedDeterminantAssociationStatement.{u, uV, uP} := by
  intro c hc F E _ _ _ _ _ _ _ r S T P ω hω hP
  have hClass := (isWeaklyAssociatedClass_isoClass_iff S T).mpr ⟨P, hP⟩
  obtain ⟨δ, _, hδ, hUnique, _⟩ := associatedCentralCharacter c hc F E S T hClass
  rw [hUnique ω hω]
  exact hδ

/-- Weak association transfers to any actual presentation of a finite-order twist. -/
theorem presentedTwistAssociation : PresentedTwistAssociationStatement.{u, uV, uP, uQ} := by
  intro c hc F E _ _ _ _ _ _ _ r S T T' P P' χ hTwist hP
  let Tχ := T.determinantTwist χ hTwist.1
  let Pχ := P.determinantTwist χ hTwist.1
  have hχ := presentedDeterminantMultipleAssociation c hc F E S T Tχ P Pχ χ
    (Automorphic.OperatorRealization.isDeterminantMultiple_determinantTwist
      T.realization χ hTwist.1) hP
  have hClass := (isWeaklyAssociatedClass_isoClass_iff _ Tχ).mpr ⟨Pχ, hχ⟩
  have he : Tχ.isoClass = T'.isoClass :=
    (Tχ.isoClass_eq_iff T').mpr
      ((T.determinantTwist_isFiniteOrderDeterminantTwist χ hTwist.1).target_equivalent hTwist)
  rw [he] at hClass
  exact hClass.presentation P'

/-- The twist of the relative Weil representation is weakly associated with the
twisted cuspidal class, using a presentation in the requested carrier universe. -/
theorem classTwistAssociation : ClassTwistAssociationStatement.{u, uV, uP, uQ} := by
  intro c hc F E _ _ _ _ _ _ _ r S π π' χ hTwist hAssoc
  revert hTwist hAssoc
  refine Quotient.inductionOn₂ π π' ?_
  intro T T' hTwist hAssoc
  obtain ⟨P, hP⟩ := (isWeaklyAssociatedClass_isoClass_iff S T).mp hAssoc
  obtain ⟨A, hI, hA⟩ := Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence F r T'
  obtain ⟨Q, hQ⟩ := T'.exists_presentation_of_finiteSlice A hI hA
  obtain ⟨P', _⟩ := Q.exists_small hQ
  apply (isWeaklyAssociatedClass_isoClass_iff _ T').mpr
  exact ⟨P', presentedTwistAssociation c hc F E S T T' P P' χ hTwist hP⟩

/-- Henniart's determinant and finite-order twist assertions for presented relative
Weil representations and cuspidal automorphic classes. -/
theorem associatedDeterminantTwist : AssociatedDeterminantTwistStatement.{u, uV, uP, uQ} :=
  ⟨presentedDeterminantAssociation, presentedTwistAssociation, classTwistAssociation⟩

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
