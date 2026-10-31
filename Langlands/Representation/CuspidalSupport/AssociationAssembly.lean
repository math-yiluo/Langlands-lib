import Langlands.Representation.CuspidalSupport.AssociationForwardStatement
import Langlands.Representation.CuspidalSupport.AssociationReverseStatement
import Langlands.Representation.CuspidalSupport.AssociationLawsStatement
import Langlands.Representation.CuspidalSupport.AssociationRankZeroProof
import Langlands.Representation.Filtration.CommonSubquotientProof
import Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof

/-! Logical assembly of cuspidal-induction association. The analytic inputs are
explicit here and are discharged in AssociationProof. -/

namespace Langlands.CuspidalSupport.AssociationAssembly

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

/-- The target induction is Artinian; the eventual length theorem supplies this. -/
def ArtinianInput : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (C : BlockShape n)
    (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
    τ.IsIrreducible → IsLeviCuspidal C τ.representation →
    IsArtinian (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (T.normalizedParabolicInduced C τ.representation).asModule

/-- A conditional assembly of the literal positive-rank target. -/
theorem positiveRank
    (hHom : AssociatedCuspidalInductionHomTheorem.{uF, uV, uW})
    (hHomSelf : AssociatedCuspidalInductionHomTheorem.{uF, uV, uV})
    (hRefl : RepresentationAssociationReflexivityTheorem.{uF, uV})
    (hFactors : AssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW})
    (hn : 0 < n)
    (hArt : ArtinianInput.{uF, uW} F T n)
    (hReverse : CuspidalInductionReverseAssociationTheorem.{uF, uV, uW} F T n) :
    CuspidalInductionAssociationTheorem.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hσ hcσ hτ hcτ
  let A := SmoothRep.of (T.normalizedParabolicInduced B σ.representation)
    (T.isSmooth_normalizedParabolicInduced B σ.representation)
  let A' := SmoothRep.of (T.normalizedParabolicInduced C τ.representation)
    (T.isSmooth_normalizedParabolicInduced C τ.representation)
  change
    (RepresentationsAssociated B C σ.representation τ.representation ↔
      ∃ f : A.representation.IntertwiningMap A'.representation, f ≠ 0) ∧
    (RepresentationsAssociated B C σ.representation τ.representation ↔
      HaveSameJordanHolderFactors A.obj A'.obj) ∧
    (RepresentationsAssociated B C σ.representation τ.representation ↔
      HaveCommonIrreducibleSubquotient A A')
  have hA : Nontrivial A := by
    obtain ⟨f, hf⟩ := hHomSelf p F T n hn B B σ σ hσ hcσ hσ hcσ
      (hRefl F.Carrier n B σ σ.representation)
    rcases subsingleton_or_nontrivial A with h | h
    · let := h
      exact False.elim (hf (by
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro v
        exact Subsingleton.elim _ _))
    · exact h
  have homCommon :
      (∃ f : A.representation.IntertwiningMap A'.representation, f ≠ 0) →
        HaveCommonIrreducibleSubquotient A A' :=
    nonzeroHomCommonSubquotient ℂ (GeneralLinear n F.Carrier) A A'
      (hArt C τ hτ hcτ)
  have factorsCommon : HaveSameJordanHolderFactors A.obj A'.obj →
      HaveCommonIrreducibleSubquotient A A' :=
    sameFactorsCommonSubquotient A A' hA
  have commonAssociated : HaveCommonIrreducibleSubquotient A A' →
      RepresentationsAssociated B C σ.representation τ.representation :=
    hReverse B C σ τ hσ hcσ hτ hcτ
  have associatedHom :
      RepresentationsAssociated B C σ.representation τ.representation →
      ∃ f : A.representation.IntertwiningMap A'.representation, f ≠ 0 :=
    hHom p F T n hn B C σ τ hσ hcσ hτ hcτ
  exact ⟨⟨associatedHom, fun h => commonAssociated (homCommon h)⟩,
    ⟨hFactors p F T n hn B C σ τ hσ hcσ hτ hcτ,
      fun h => commonAssociated (factorsCommon h)⟩,
    ⟨fun h => homCommon (associatedHom h), commonAssociated⟩⟩

/-- The finite-length conclusion supplies precisely the Artinian input. -/
theorem artinianInput_of_length
    (hLength : CuspidalInductionLengthTheorem.{uF, uW} F T n) :
    ArtinianInput.{uF, uW} F T n := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro C τ hτ hcτ
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (hLength C τ hτ hcτ).1).2

/-- Conditional assembly for every rank, using the published rank-zero proof. -/
theorem allRanks
    (hHom : AssociatedCuspidalInductionHomTheorem.{uF, uV, uW})
    (hHomSelf : AssociatedCuspidalInductionHomTheorem.{uF, uV, uV})
    (hRefl : RepresentationAssociationReflexivityTheorem.{uF, uV})
    (hFactors : AssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW})
    (hLength : ∀ m, 0 < m → CuspidalInductionLengthTheorem.{uF, uW} F T m)
    (hReverse : ∀ m, 0 < m → CuspidalInductionReverseAssociationTheorem.{uF, uV, uW} F T m) :
    CuspidalInductionAssociationTheorem.{uF, uV, uW} F T n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact cuspidalInductionAssociationRankZero p F T
  · exact positiveRank F T n hHom hHomSelf hRefl hFactors hn
      (artinianInput_of_length F T n (hLength n hn)) (hReverse n hn)

end Langlands.CuspidalSupport.AssociationAssembly
