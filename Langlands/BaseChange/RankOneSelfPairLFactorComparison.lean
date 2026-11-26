import Langlands.BaseChange.NormTwistFibreReduction
import Langlands.BaseChange.PadicCharacterNormFactors
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction
import Langlands.Representation.GodementJacquet.TateCharacterLFactor
import Langlands.Representation.GodementJacquet.TateCharacterReduction
import Langlands.Representation.Unramified.PrincipalSeriesDuality

/-! # The self-pair Euler comparison in rank one -/

noncomputable section

set_option autoImplicit false

universe u v uV uW

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis LocalClassField RankinSelberg
open LocalFactor.PadicAbelian (SelfDualHaar lPolynomial)
open scoped BigOperators

section CharacterModel

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

private local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
private local instance : IsTopologicalGroup (GeneralLinear 1 K.Carrier) :=
  K.canonicalTopologicalData.generalLinearTopologicalGroup 1

private theorem rankOne_twistedSelfPairPolynomial
    (ψ : UnitaryAdditiveCharacter K.Carrier)
    (ν : SelfDualHaar K.canonicalTopologicalData ψ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear 1 K.Carrier) V) (ha : IsAdmissible ρ)
    (hi : ρ.IsIrreducible) (κ : Quasicharacter K.Carrier) :
    IsPadicRankLPolynomial K ψ ν.val ρ
      (twist (κ.toMonoidHom.comp determinant) (smoothContragredient ρ))
      (lPolynomial K.canonicalTopologicalData κ) := by
  obtain ⟨χ, ⟨e⟩⟩ := GodementJacquet.exists_tateCharacterModel ρ ha hi
  let ed : (smoothContragredient ρ).Equiv (rankOneCharacter (χ⁻¹).toMonoidHom) :=
    (smoothContragredientEquiv e).symm.trans (Unramified.scalarCharacterSmoothDualEquiv K χ)
  have ht : twist (κ.toMonoidHom.comp determinant) (rankOneCharacter (χ⁻¹).toMonoidHom) =
      rankOneCharacter ((κ * χ⁻¹ : Quasicharacter K.Carrier).toMonoidHom) := by
    ext g
    simp [rankOneCharacter, characterRepresentation, twist]
  let et := (twistEquiv (κ.toMonoidHom.comp determinant) ed).trans (equivOfRepresentationEq ht)
  have h := GodementJacquet.Padic.rankOneCharacters_isPadicPairLPolynomial K χ ψ (κ * χ⁻¹) ν.val
  have hm : χ * (κ * χ⁻¹) = κ := by
    apply ContinuousMonoidHom.ext
    intro x
    change χ x * (κ x * (χ x)⁻¹) = κ x
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  rw [hm] at h
  exact isPadicRankLPolynomial_succ.mpr
    ((IsPadicSymmetricLPolynomial.congr_equiv e et).mpr
      ((isPadicSymmetricLPolynomial_of_le le_rfl).mpr h))

end CharacterModel

/-- The rank-one self-pair identity for actual admissible irreducible actions.
In rank one the scalar actions cancel with their duals, so no compatibility
between the lower and upper actions is needed. -/
def RankOneSelfPairLFactorComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := E.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := E.canonicalTopologicalData.localField
    ∀ f : ℕ, IsResidueDegree F.Carrier E.Carrier f →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear 1 F.Carrier) V)
      (P : Representation ℂ (GeneralLinear 1 E.Carrier) W),
      IsAdmissible π → π.IsIrreducible → IsAdmissible P → P.IsIrreducible →
    ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (νF : SelfDualHaar F.canonicalTopologicalData ψF)
      (ψE : UnitaryAdditiveCharacter E.Carrier) (νE : SelfDualHaar E.canonicalTopologicalData ψE)
      (X : Finset (F.Carrierˣ →* ℂˣ)),
      (∀ κ, κ ∈ X ↔ IsNormTrivial E.Carrier κ) →
    ∀ (Q_E : Polynomial ℂ) (Q_F : X → Polynomial ℂ),
      IsPadicRankLPolynomial E ψE νE.val P (smoothContragredient P) Q_E →
      (∀ κ : X, IsPadicRankLPolynomial F ψF νF.val π
        (twist (κ.val.comp determinant) (smoothContragredient π)) (Q_F κ)) →
      Q_E.comp (Polynomial.X ^ f) = ∏ κ : X, Q_F κ

/-- In rank one the certified self-pair factors reduce to the abelian norm
comparison for the trivial quasicharacter. -/
theorem rankOneSelfPairLFactorComparison : RankOneSelfPairLFactorComparisonStatement.{u,v,uV,uW} := by
  intro p _ F E _ _ _
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro f hf V _ _ W _ _ π P haπ hiπ haP hiP ψF νF ψE νE X hX QE QF hQE hQF
  let : NontriviallyNormedField F.Carrier := F.canonicalNormedField
  let : CompleteSpace F.Carrier := inferInstance
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let ξ (κ : X) : Quasicharacter F.Carrier := ⟨κ.val,
    CuspidalSupport.NormalHecke.continuous_of_isOpen_ker κ.val ((hX _).mp κ.property).isOpen_ker⟩
  have hl (κ : X) : QF κ = lPolynomial T (ξ κ) :=
    (hQF κ).unique (rankOne_twistedSelfPairPolynomial F ψF νF π haπ hiπ (ξ κ))
  have hu : QE = lPolynomial S (1 : Quasicharacter E.Carrier) := by
    apply hQE.unique
    have h := rankOne_twistedSelfPairPolynomial E ψE νE P haP hiP 1
    have ht : twist ((1 : Quasicharacter E.Carrier).toMonoidHom.comp determinant)
        (smoothContragredient P) = smoothContragredient P := by
      ext g x
      simp [twist]
    rwa [ht] at h
  have hab := prod_lPolynomial_normTwists T S hf (1 : Quasicharacter F.Carrier) X hX ξ
    (fun κ => (mul_one κ.val).symm)
  have he : (1 : Quasicharacter F.Carrier).comp (localNorm T S) = 1 := by
    ext x
    rfl
  rw [he, Polynomial.expand_eq_comp_X_pow] at hab
  rw [hu]
  simp_rw [hl]
  exact hab.symm

end Langlands.BaseChange
