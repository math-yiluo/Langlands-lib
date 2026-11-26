import Langlands.Representation.RankinSelberg.FieldTransport.LocalFieldEpsilon

/-! # Normalized JPSS Euler polynomials under local-field isomorphisms -/

noncomputable section

set_option autoImplicit false

namespace Langlands.RankinSelberg.FieldTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe u v uV uW

variable {F : Type u} {E : Type v} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E] [ValuativeRel F] [ValuativeRel E]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  {ν : letI := borel F; AdditiveHaarMeasure F}
  {ν' : letI := borel E; AdditiveHaarMeasure E}
  (hψ : ∀ x, ψ' (σ x) = ψ x)
  (hν : letI := borel F; letI := borel E; ν'.measure = ν.measure.map σ)
  {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GeneralLinear (r + 1) E) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) E) W) (P : Polynomial ℂ)

include hψ hν in
/-- The normalized JPSS polynomial is invariant under pullback of the pair,
the additive character and the additive Haar measure. -/
theorem isLocalPairLPolynomial_comp_iff :
    AllField.RankinSelberg.IsPadicPairLPolynomial E ψ' ν' π τ P ↔
      AllField.RankinSelberg.IsPadicPairLPolynomial F ψ ν
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) P := by
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel E
  let : BorelSpace E := ⟨rfl⟩
  let := borel (GeneralLinear (n + 1) F)
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (GeneralLinear (n + 1) E)
  let : BorelSpace (GeneralLinear (n + 1) E) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) E)
  let : BorelSpace (upperUnipotent (n + 1) E) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n E)
  let : BorelSpace (LeftUnipotentQuotient n E) := ⟨rfl⟩
  let : SigmaCompactSpace F := TF.sigmaCompactSpace
  let : SigmaCompactSpace E := TE.sigmaCompactSpace
  have hO (x : F) : σ x ∈ (ValuativeRel.valuation E).integer ↔
      x ∈ (ValuativeRel.valuation F).integer :=
    (TF.mem_integers_iff_of_continuous_ringEquiv TE σ hσ hσs x).symm
  have hU := (unipotentHaar_map σ hσ hσs hO n).symm
  have hG := (generalLinearHaar_map σ hσ hσs hO n).symm
  have habv (x : F) : AllField.RankinSelberg.normalizedAbsoluteValue TE (σ x) =
      AllField.RankinSelberg.normalizedAbsoluteValue TF x :=
    TF.normalizedAbs_of_continuous_ringEquiv TE σ hσ hσs x
  have hinv := isMulRightInvariant_unipotentHaar_iff σ hσ hσs hU
  unfold AllField.RankinSelberg.IsPadicPairLPolynomial
  rw [show (⟨⟩ : LocalFieldData E).residueCardinality = (⟨⟩ : LocalFieldData F).residueCardinality
    from TF.residueCardinality_of_continuous_ringEquiv TE σ hσ hσs]
  constructor
  · rintro ⟨⟨hE, hcE⟩, hall⟩
    have hF := hinv.mp hE
    refine ⟨⟨hF, (compatibleMeasureExists_unipotentHaar_iff σ hσ hσs hG hU).mp hcE⟩, ?_⟩
    intro _ μ hμ
    exact (isPairLPolynomial_comp_iff σ hσ hσs hψ habv _ μ ν ν' hν π τ P).mp
      (hall (μ.map (quotientHomeomorph σ hσ hσs n))
        ((isCompatible_unipotentHaar_map_iff σ hσ hσs hG hU μ).mpr hμ))
  · rintro ⟨⟨hF, hcF⟩, hall⟩
    have hE := hinv.mpr hF
    refine ⟨⟨hE, (compatibleMeasureExists_unipotentHaar_iff σ hσ hσs hG hU).mpr hcF⟩, ?_⟩
    intro _ μ₂ hμ₂
    obtain ⟨μ, rfl⟩ := exists_map_eq (fieldEquiv (n + 1) σ hσ hσs)
      (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs) μ₂
    exact (isPairLPolynomial_comp_iff σ hσ hσs hψ habv _ μ ν ν' hν π τ P).mpr
      (hall μ ((isCompatible_unipotentHaar_map_iff σ hσ hσs hG hU μ).mp hμ₂))

end Langlands.RankinSelberg.FieldTransport
