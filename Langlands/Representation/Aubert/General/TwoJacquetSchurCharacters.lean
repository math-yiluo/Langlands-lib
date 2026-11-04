import Langlands.Representation.Aubert.General.CentralCharacterInheritance
import Langlands.Representation.Aubert.General.TwoJacquetFactorExponents
import Langlands.Representation.Smooth.Schur.Proof

/-! # Actual scalar characters for two simple Jacquet images -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L O : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hO : IsSemidirectDecomposition Q L O) (hOc : IsClosed (O : Set G))
  (σ : SmoothRep.{0, uG, uV} ℂ M)
  (hσ : σ.IsIrreducible) (haσ : σ.IsAdmissible)
  (hJacO : ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
    ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
  (haJacO : ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
    ((normalizedInductionFunctor h hU).obj σ)).IsAdmissible)

/-- Admissible Schur constructs the two full-center scalar characters on
the actual inducing object and second Jacquet image. -/
def inductionTwoJacquetScalarCharactersOfSchur :
    InductionTwoJacquetScalarCharacters h hU hO hOc σ := by
  let first := (admissibleSchur_centralCharacter σ.representation haσ hσ).choose
  let second := (admissibleSchur_centralCharacter
    ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation haJacO hJacO).choose
  exact {
    first := first
    first_scalar :=
      (admissibleSchur_centralCharacter σ.representation haσ hσ).choose_spec.1.2
    second := second
    second_scalar := (admissibleSchur_centralCharacter
      ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
        ((normalizedInductionFunctor h hU).obj σ)).representation haJacO hJacO).choose_spec.1.2 }

theorem inductionTwoJacquetScalarCharactersOfSchur_first_isOpen_ker :
    IsOpen ((inductionTwoJacquetScalarCharactersOfSchur
      h hU hO hOc σ hσ haσ hJacO haJacO).first.ker : Set (Subgroup.center M)) :=
  (admissibleSchur_centralCharacter σ.representation haσ hσ).choose_spec.1.1.isOpen_fiber 1

theorem inductionTwoJacquetScalarCharactersOfSchur_second_isOpen_ker :
    IsOpen ((inductionTwoJacquetScalarCharactersOfSchur
      h hU hO hOc σ hσ haσ hJacO haJacO).second.ker : Set (Subgroup.center L)) :=
  (admissibleSchur_centralCharacter
    ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation
        haJacO hJacO).choose_spec.1.1.isOpen_fiber 1

include hJacO in
/-- Simplicity of the second actual Jacquet image already forces the
whole induction to be nonzero. No induction finite-length premise is used. -/
theorem nontrivial_induction_of_irreducible_secondJacquet :
    Nontrivial ((normalizedInductionFunctor h hU).obj σ) := by
  let A := (normalizedInductionFunctor h hU).obj σ
  have hn : Nontrivial ((jacquetFunctor.{uG, max uG uV} hO hOc).obj A) :=
    repLength_pos_iff.mp (by
      rw [repLength_eq_one_iff.mpr hJacO]
      exact zero_lt_one)
  let : Nontrivial (Jacquet.Localization.Coinvariants A.representation O 1) := hn
  exact (Jacquet.Localization.mk_surjective A.representation O 1).nontrivial

include hJacO in
/-- For either choice of scalar characters, the first character is unitary
on the ambient center when the actual induction has unitary central character. -/
theorem InductionTwoJacquetScalarCharacters.first_norm_ambientCenter_eq_one
    (C : InductionTwoJacquetScalarCharacters h hU hO hOc σ)
    (hZM : Subgroup.center G ≤ M)
    (c : UnitaryCentralCharacter
      ((normalizedInductionFunctor h hU).obj σ).representation)
    (z : Subgroup.center G) :
    ‖(C.first (ambientCenterToLeviCenter M hZM z) : ℂ)‖ = 1 := by
  let := nontrivial_induction_of_irreducible_secondJacquet h hU hO hOc σ hJacO
  exact norm_inducingScalar_ambientCenter_eq_one h hU hZM σ c
    C.first C.first_scalar z

include hJacO in
/-- The second scalar character has the same ambient unit-modulus property
on the actual normalized Jacquet module of that induction. -/
theorem InductionTwoJacquetScalarCharacters.second_norm_ambientCenter_eq_one
    (C : InductionTwoJacquetScalarCharacters h hU hO hOc σ)
    (hZL : Subgroup.center G ≤ L)
    (c : UnitaryCentralCharacter
      ((normalizedInductionFunctor h hU).obj σ).representation)
    (z : Subgroup.center G) :
    ‖(C.second (ambientCenterToLeviCenter L hZL z) : ℂ)‖ = 1 := by
  have hn : Nontrivial ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
      ((normalizedInductionFunctor h hU).obj σ)) :=
    repLength_pos_iff.mp (by
      rw [repLength_eq_one_iff.mpr hJacO]
      exact zero_lt_one)
  let : Nontrivial ((normalizedJacquetFunctor O L hOc hO.levi_le_normalizer).obj
      ((normalizedInductionFunctor h hU).obj σ)) := hn
  exact norm_jacquetScalar_ambientCenter_eq_one O L hOc hO.levi_le_normalizer hZL
    ((normalizedInductionFunctor h hU).obj σ) c C.second C.second_scalar z

end Langlands.Aubert.General
