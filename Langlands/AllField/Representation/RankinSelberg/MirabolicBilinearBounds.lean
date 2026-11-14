import Langlands.Representation.RankinSelberg.MirabolicBilinearBounds
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
import Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer
/-! Actual mirabolic specialization and translation of finite spectral exceptions. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement mirabolic_exists_exception_length_le_one mirabolic_shift_length_bound normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.InvariantBilinear

universe uF uV uW

/-- Finite mirabolic length and irreducible pair control give the full bilinear
bound for actual restrictions of representations with one-dimensional functionals. -/
theorem mirabolic_exists_exception_length_le_one
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (θ θ' : GeneralLinear.upperUnipotent (n + 1) F →* ℂˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (_hρ : IsSmooth ρ) (_hσ : IsSmooth σ)
      (_eρ : functionals (GeneralLinear.upperUnipotent (n + 1) F) θ ρ ≃ₗ[ℂ] ℂ)
      (_eσ : functionals (GeneralLinear.upperUnipotent (n + 1) F) θ' σ ≃ₗ[ℂ] ℂ)
      (_hfinρ : IsFiniteLength (MonoidAlgebra ℂ (mirabolic n F))
        (Representation.asModule (ρ.comp (mirabolic n F).subtype)))
      (_hfinσ : IsFiniteLength (MonoidAlgebra ℂ (mirabolic n F))
        (Representation.asModule (σ.comp (mirabolic n F).subtype))),
      (∀ (C : Rep.{uV} ℂ (mirabolic n F))
        (D : Rep.{uW} ℂ (mirabolic n F)),
        IsSmooth C.ρ → IsSmooth D.ρ →
        Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          (length C.ρ D.ρ
            (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≠ 0 →
            HasFunctional (N := Mirabolic.upperUnipotent n F)
              (θ := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) C.ρ ∧
            HasFunctional (N := Mirabolic.upperUnipotent n F)
              (θ := θ'.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) D.ρ) ∧
          (HasFunctional (N := Mirabolic.upperUnipotent n F)
              (θ := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) C.ρ →
            HasFunctional (N := Mirabolic.upperUnipotent n F)
              (θ := θ'.comp Mirabolic.upperUnipotentEquiv.toMonoidHom) D.ρ →
            length C.ρ D.ρ
              (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1)) →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        length (ρ.comp (mirabolic n F).subtype)
          (σ.comp (mirabolic n F).subtype)
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ hσ eρ eσ hfinρ hfinσ hpair
  let ρP := ρ.comp (mirabolic n F).subtype
  let σP := σ.comp (mirabolic n F).subtype
  let U := Mirabolic.upperUnipotent n F
  let θP := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  let θP' := θ'.comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  let eρP : functionals U θP ρP ≃ₗ[ℂ] ℂ :=
    (mirabolicFunctionalsEquiv θ ρ).symm.trans eρ
  let eσP : functionals U θP' σP ≃ₗ[ℂ] ℂ :=
    (mirabolicFunctionalsEquiv θ' σ).symm.trans eσ
  have hρP : IsSmooth ρP := isSmooth_comp _ continuous_subtype_val hρ
  have hσP : IsSmooth σP := isSmooth_comp _ continuous_subtype_val hσ
  have hfunρ : HasFunctional (N := U) (θ := θP) ρP :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ eρP]
      exact one_ne_zero)
  have hfunσ : HasFunctional (N := U) (θ := θP') σP :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ eσP]
      exact one_ne_zero)
  have hU := Langlands.AllField.GeneralLinear.Mirabolic.upperUnipotent_isLimitOfCompactSubgroups F T n
  exact exists_exception_length_le_one_of_finiteLength U U hU hU θP θP'
    (character_isLocallyConstant_of_hasFunctional _ _ _ hρP hfunρ)
    (character_isLocallyConstant_of_hasFunctional _ _ _ hσP hfunσ)
    (spectralPoint T.residueCardinality)
    (fun s g => determinantWeight (normalizedAbsoluteValue T) g.val (-s))
    (Rep.of ρP) (Rep.of σP) hρP hσP hfinρ hfinσ eρP eσP hpair

/-- The minus-parameter mirabolic bound supplies the exact Frobenius weight `1-s`. -/
theorem mirabolic_shift_length_bound
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (mirabolic n F) V)
    (σ : Representation ℂ (mirabolic n F) W)
    (h : ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      length ρ σ (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1) :
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      length ρ σ (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)) ≤ 1 := by
  have h' := exists_finite_exception_shift T.residueCardinality T.residueCardinality_gt_one
    (-1) (fun s => length ρ σ
      (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≤ 1) h
  simpa only [neg_add_rev, neg_neg, sub_eq_add_neg] using h'

end Langlands.AllField.RankinSelberg
