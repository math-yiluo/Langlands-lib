import Langlands.Representation.RankinSelberg.SupercuspidalParameterProductStatement
import Langlands.Representation.RankinSelberg.SupercuspidalParameterDualityProof
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.Classification.SupercuspidalInverseTranspose
import Langlands.Representation.CuspidalSupport.AssociationReduction

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial GeneralLinear Whittaker HarmonicAnalysis SegmentGammaTelescoping

universe uF uV uW

section Certification

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W}

local instance productTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- Any exact unit-indexed parameter set certifies the equal-rank product. -/
private theorem parameter_product_of_exact
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hπ : π.IsIrreducible) (hπs : IsSupercuspidal π)
    (hσ : σ.IsIrreducible)
    (hσw : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (A : Finset ℂˣ)
    (hA : ∀ a : ℂˣ, a ∈ A ↔ IsContragredientTwistParameter F π σ (a : ℂ)) :
    IsPadicPairLPolynomial F ψ ν.val π σ (∏ a ∈ A, linearFactor a) := by
  classical
  obtain ⟨B, hB, hP⟩ := supercuspidalEqualRankLFactor p F ψ ν r π σ hπ hπs hσ hσw
  change ∀ b, b ∈ B ↔ IsContragredientTwistParameter F π σ b at hB
  have hBA : B = A.image (fun a : ℂˣ => (a : ℂ)) := by
    ext b
    constructor
    · intro hb
      have hp := (hB b).mp hb
      let u : ℂˣ := Units.mk0 b hp.ne_zero
      exact Finset.mem_image.mpr ⟨u, (hA u).mpr hp, rfl⟩
    · intro hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact (hB _).mpr ((hA a).mp ha)
  have hprod :
      (∏ b ∈ A.image (fun a : ℂˣ => (a : ℂ)), (1 - C b * X)) =
        ∏ a ∈ A, linearFactor a := by
    rw [Finset.prod_image]
    · rfl
    · intro a _ b _ hab
      exact Units.ext hab
  rw [hBA, hprod] at hP
  exact hP

end Certification

/-- The original and actual inverse-transpose dual products share inverse
finite unit-parameter sets. -/
theorem supercuspidalParameterProduct :
    SupercuspidalParameterProductStatement.{uF, uV, uW} := by
  classical
  intro p _ F ψ ν r V _ _ W _ _ π σ hπ hπs hσ hσw
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨B, hB⟩ :=
    exists_finset_contragredientTwistParameters F π σ hπ hσ hπs.1 hσw.1
  let unitOf : B → ℂˣ := fun b =>
    Units.mk0 b.val ((hB b.val).mp b.property).ne_zero
  let A : Finset ℂˣ := B.attach.image unitOf
  have hA : ∀ a : ℂˣ, a ∈ A ↔ IsContragredientTwistParameter F π σ (a : ℂ) := by
    intro a
    constructor
    · intro ha
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ha
      have hv : b.val = (a : ℂ) := congrArg Units.val hb
      exact hv ▸ ((hB b.val).mp b.property)
    · intro ha
      have hb : (a : ℂ) ∈ B := (hB _).mpr ha
      refine Finset.mem_image.mpr ⟨⟨(a : ℂ), hb⟩, Finset.mem_attach _ _, ?_⟩
      exact Units.ext rfl
  refine ⟨A, hA, parameter_product_of_exact ν hπ hπs hσ hσw A hA, ?_, ?_⟩
  · have hπd : (inverseTransposePullback π).IsIrreducible :=
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff π
        (inverseTranspose (r + 1) F.Carrier)).mpr hπ
    have hσd : (inverseTransposePullback σ).IsIrreducible :=
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff σ
        (inverseTranspose (r + 1) F.Carrier)).mpr hσ
    have hπds : IsSupercuspidal (inverseTransposePullback π) :=
      isSupercuspidal_comp_inverseTranspose π hπs
    have hσdw : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
        (inverseTransposePullback σ) := by
      simpa only [standardCharacter_scale_neg_one] using
        isOfWhittakerType_inverseTransposePullback ψ σ hσw
    have hAd : ∀ b : ℂˣ, b ∈ A.image (fun a : ℂˣ => a⁻¹) ↔
        IsContragredientTwistParameter F
          (inverseTransposePullback π) (inverseTransposePullback σ) (b : ℂ) := by
      intro b
      constructor
      · intro hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        simpa only [Units.val_inv_eq_inv_val] using
          (IsContragredientTwistParameter.inverseTranspose_iff
            hπs.1 hσw.1 hπ hσ (a : ℂ)).mpr ((hA a).mp ha)
      · intro hb
        have hp : IsContragredientTwistParameter F π σ ((b⁻¹ : ℂˣ) : ℂ) := by
          apply (IsContragredientTwistParameter.inverseTranspose_iff
            hπs.1 hσw.1 hπ hσ _).mp
          simpa only [Units.val_inv_eq_inv_val, inv_inv] using hb
        exact Finset.mem_image.mpr ⟨b⁻¹, (hA _).mpr hp, inv_inv b⟩
    have hPd := parameter_product_of_exact
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      hπd hπds hσd hσdw (A.image (fun a : ℂˣ => a⁻¹)) hAd
    have hprod : (∏ b ∈ A.image (fun a : ℂˣ => a⁻¹), linearFactor b) =
        ∏ a ∈ A, linearFactor a⁻¹ := by
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact inv_injective hab
    rw [hprod] at hPd
    exact hPd
  · intro hπu hσu a ha
    exact IsContragredientTwistParameter.norm_eq_one F π σ
      ((hA a).mp ha) hπ hσ hπs.1 hσw.1 hπu hσu

end Langlands.RankinSelberg
