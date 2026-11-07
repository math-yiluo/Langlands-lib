import Langlands.Global.Factors.RelativeWeilLocalEpsilon
import Langlands.Correspondence.RankOneNormalizedEpsilon
import Langlands.Correspondence.RankOneEpsilonFieldTransport
import Langlands.Correspondence.BaseReciprocityCandidate
import Langlands.LocalFactor.Abelian.NormalizedTwist
import Langlands.LocalFactor.Abelian.Transport

/-!
# Rank-one factors of the local virtual identity on the original fields

The rank-one factors in `conditionalPairEpsilonValue_eq_of_virtualIdentity` are abelian
epsilon expressions on intermediate fields of the common closure. They are moved to Tate's
`PadicAbelian.epsilon` on the original fields, the base field `F` and the standalone
extensions `E_j`. The characters are written through the components of the system's
normalized reciprocity family, transported to these fields. Additive characters are
moved by the field isomorphisms and the trace, and Haar measures by pushforward.
-/

noncomputable section

set_option autoImplicit false

universe u w uE uA

namespace Langlands.Weil.Local.SystemEpsilon

open LocalFactor LocalFactor.CommonClosure Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance transportBaseTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance transportBaseMeasurable : MeasurableSpace F.Carrier := borel F.Carrier

/-- The bottom-field factor of a character `RankOne.weilCharacter F e χ`, for the base
candidate `e` of a normalized family, is Tate's epsilon factor of `χ` at `s`. -/
theorem baseFactor_eq_epsilon (eC : ReciprocityFamily F) (hN : NormalizedReciprocity F eC)
    (χ : QuasiCharacter F) (ψF : NontrivialAdditiveCharacter F)
    (ψ : AdditiveCharacter F (baseExtension F)) (hψ : IsBaseCharacter F ψF ψ)
    (μ : HaarMeasure F (baseExtension F)) (s : ℂ) :
    (fieldData F (baseExtension F)).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
          (CommonClosureSpectral.character F (baseExtension F) s *
            baseRestrictedWeilCharacter F
              (RankOne.weilCharacter F (baseReciprocityCandidate F eC) χ))) ψ μ =
      PadicAbelian.epsilon F.canonicalTopologicalData χ ψF
        ((baseFieldHaarMeasureEquiv F).symm μ).measure s := by
  rw [Correspondence.fieldCharacterEquiv_mul, fieldCharacterEquiv_spectralCharacter F eC hN,
    fieldCharacterEquiv_baseRestrictedWeilCharacter F (baseReciprocityCandidate_spec F eC) χ,
    ← baseFieldCharacterEquiv_normalizedAbsPowerCharacter, ← baseFieldCharacterEquiv_mul,
    abelianEpsilonExpression_of_isBaseCharacter F _ ψF ψ hψ μ,
    PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul]

section Image

variable (E : PadicField.{u} p) (g : F.Carrier →ₐ[Padic p] E.Carrier)

local instance transportImageTopology : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology

local instance transportImageMeasurable : MeasurableSpace E.Carrier := borel E.Carrier

local instance transportImageAlgebra :
    Algebra (Padic p) (LocalClassField.extensionFiniteIntermediate F E g).field :=
  ((LocalClassField.extensionFiniteIntermediate F E g).asPadicField (p := p)).algebra

local instance transportImageFieldTopology :
    TopologicalSpace (LocalClassField.extensionFiniteIntermediate F E g).field :=
  (fieldData F (LocalClassField.extensionFiniteIntermediate F E g)).topology

/-- For a normalized family, the field character of the image of `E` obtained from
`|·|_E^s η` by field transport pulls back to `ω_s` times the image character of
`η ∘ rec`, where `rec` is the family's component transported to `E`. -/
theorem weilCharacter_imageQuasicharacter (eC : ReciprocityFamily F)
    (hN : NormalizedReciprocity F eC) (η : QuasiCharacter E) (s : ℂ) :
    CommonClosure.weilCharacter F eC (LocalClassField.extensionFiniteIntermediate F E g)
        (PadicField.ConductorTransport.quasicharacter E
          ((LocalClassField.extensionFiniteIntermediate F E g).asPadicField (p := p))
          (LocalClassField.extensionIntermediatePadicEquiv F E g)
          (E.canonicalTopologicalData.normalizedAbsPowerCharacter s * η)) =
      CommonClosureSpectral.character F _ s *
        imageCharacter F E g
          (RankOne.weilCharacter E (LocalClassField.extensionReciprocityCandidate F E g eC) η) := by
  apply ContinuousMonoidHom.ext
  intro w
  obtain ⟨v, rfl⟩ := (LocalClassField.extensionImageWeilEquiv F E g).surjective w
  have hu : (LocalClassField.extensionIntermediateUnitsEquiv F E g).symm
      (reciprocityUnits F eC _ (LocalClassField.extensionImageWeilEquiv F E g v)) =
      RankOne.reciprocityUnits E (LocalClassField.extensionReciprocityCandidate F E g eC) v :=
    rfl
  apply Units.ext
  change ((E.canonicalTopologicalData.normalizedAbsPowerCharacter s * η)
      ((LocalClassField.extensionIntermediateUnitsEquiv F E g).symm
        (reciprocityUnits F eC _ (LocalClassField.extensionImageWeilEquiv F E g v))) : ℂ) =
    (CommonClosureSpectral.character F _ s (LocalClassField.extensionImageWeilEquiv F E g v) : ℂ) *
      (η (RankOne.reciprocityUnits E (LocalClassField.extensionReciprocityCandidate F E g eC)
        ((LocalClassField.extensionImageWeilEquiv F E g).symm
          (LocalClassField.extensionImageWeilEquiv F E g v))) : ℂ)
  rw [ContinuousMulEquiv.symm_apply_apply, ContinuousMonoidHom.mul_apply, Units.val_mul,
    PadicField.TopologicalData.normalizedAbsPowerCharacter_apply,
    LocalClassField.extensionIntermediateUnitsEquiv_symm_normalizedAbs,
    CommonClosureSpectralAnalytic.character_eq_norm_exp F eC _ hN, hu]

/-- The factor of the image of `E` in the main theorem, for `α = η ∘ rec`, the transported
additive character of `ψE` and the transported Haar measure of `μE`, is Tate's epsilon factor
of `η` at `s`. -/
theorem imageFactor_eq_epsilon (eC : ReciprocityFamily F) (hN : NormalizedReciprocity F eC)
    (η : QuasiCharacter E) (ψE : NontrivialAdditiveCharacter E)
    (μE : LocalAdditiveHaarMeasure E) (s : ℂ) :
    (fieldData F (LocalClassField.extensionFiniteIntermediate F E g)).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC _
          (CommonClosureSpectral.character F _ s *
            imageCharacter F E g
              (RankOne.weilCharacter E (LocalClassField.extensionReciprocityCandidate F E g eC) η)))
        (CommonClosureSystemTransport.imageAdditiveCharacter F E g ψE)
        (CommonClosureSystemTransport.imageHaarMeasure F E g μE) =
      PadicAbelian.epsilon E.canonicalTopologicalData η ψE μE.measure s := by
  have hq : CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC _
      (CommonClosureSpectral.character F _ s *
        imageCharacter F E g
          (RankOne.weilCharacter E (LocalClassField.extensionReciprocityCandidate F E g eC) η)) =
      (PadicField.ConductorTransport.quasicharacter E
        ((LocalClassField.extensionFiniteIntermediate F E g).asPadicField (p := p))
        (LocalClassField.extensionIntermediatePadicEquiv F E g)
        (E.canonicalTopologicalData.normalizedAbsPowerCharacter s * η) :
        FieldCharacter F (LocalClassField.extensionFiniteIntermediate F E g)) := by
    rw [← weilCharacter_imageQuasicharacter F E g eC hN η s]
    exact fieldCharacterEquiv_weilCharacter F eC _ _
  refine (congrArg (fun χ => (fieldData F _).abelianEpsilonExpression χ
    (CommonClosureSystemTransport.imageAdditiveCharacter F E g ψE)
    (CommonClosureSystemTransport.imageHaarMeasure F E g μE)) hq).trans ?_
  refine (PadicField.AbelianTransport.abelianEpsilonExpression_eq E
    ((LocalClassField.extensionFiniteIntermediate F E g).asPadicField (p := p))
    (LocalClassField.extensionIntermediatePadicEquiv F E g) _ ψE μE).trans ?_
  exact PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul _ η ψE μE s

/-- The trace character `ψF ∘ Tr_{E/F}` on the standalone extension `E`. -/
def standaloneTraceCharacter (ψF : NontrivialAdditiveCharacter F) : NontrivialAdditiveCharacter E :=
  letI := Weil.Local.extensionAlgebra F E g
  haveI := Weil.Local.extensionAlgebra_isScalarTower F E g
  F.canonicalTopologicalData.traceCharacter E.canonicalTopologicalData ψF

/-- The trace from the image of `E` to the bottom field corresponds to the trace of
`E / F` under the field isomorphisms `E ≃ L` and `⊥ ≃ F`. -/
theorem botEquiv_trace_eq (y : (LocalClassField.extensionFiniteIntermediate F E g).field) :
    IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
        (@Algebra.trace (baseExtension F).field
          (LocalClassField.extensionFiniteIntermediate F E g).field _ _
          (IntermediateField.inclusion (baseExtension_le F _)).toAlgebra y) =
      @Algebra.trace F.Carrier E.Carrier _ _ (Weil.Local.extensionAlgebra F E g)
        ((LocalClassField.extensionIntermediatePadicEquiv F E g).symm y) := by
  let := Weil.Local.extensionAlgebra F E g
  let : Algebra (baseExtension F).field (LocalClassField.extensionFiniteIntermediate F E g).field :=
    (IntermediateField.inclusion (baseExtension_le F _)).toAlgebra
  let e₁ : F.Carrier ≃+* (baseExtension F).field :=
    (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.toRingEquiv
  let e₂ : E.Carrier ≃+* (LocalClassField.extensionFiniteIntermediate F E g).field :=
    (LocalClassField.extensionIntermediatePadicEquiv F E g).toRingEquiv
  have he : (algebraMap (baseExtension F).field
      (LocalClassField.extensionFiniteIntermediate F E g).field).comp (e₁ : F.Carrier →+* _) =
      (e₂ : E.Carrier →+* _).comp (algebraMap F.Carrier E.Carrier) := by
    ext a
    change (algebraMap F.Carrier (AlgebraicClosure F.Carrier) a) =
      LocalClassField.extensionIntermediatePadicEquiv F E g (algebraMap F.Carrier E.Carrier a)
    rw [LocalClassField.extensionIntermediatePadicEquiv_coe]
    exact (Weil.Local.extensionFieldEmbedding_comp F E g a).symm
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he (e₂.symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The bottom-field trace character, for a base additive character of `ψF`, is the
transport of `ψF ∘ Tr_{E/F}` to the image of `E`. -/
theorem traceCharacter_eq_imageAdditiveCharacter (ψF : NontrivialAdditiveCharacter F)
    (ψ : AdditiveCharacter F (baseExtension F)) (hψ : IsBaseCharacter F ψF ψ) :
    traceCharacter F (baseExtension F) (LocalClassField.extensionFiniteIntermediate F E g)
        (baseExtension_le F _) ψ =
      CommonClosureSystemTransport.imageAdditiveCharacter F E g
        (standaloneTraceCharacter F E g ψF) := by
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro y
  change ψ _ = ψF _
  rw [hψ]
  exact congrArg ψF.toAddChar (botEquiv_trace_eq F E g y)

end Image

section Assembled

local instance transportPadicTopology (K : PadicField.{u} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance transportPadicMeasurable (K : PadicField.{u} p) : MeasurableSpace K.Carrier :=
  borel K.Carrier

open WeilDeligneRepresentation VirtualRepresentation ExactGrothendieckGroup in
/-- Tate's epsilon factors in the arithmetic pair epsilon value of a local virtual identity.
Write the characters of the identity as `α₀ = χ₀ ∘ rec_F` and `α_j = η_j ∘ rec_{E_j}`,
`β_j = η'_j ∘ rec_{E_j}`. Here `rec_F` and `rec_{E_j}` are the components of the system's
normalized reciprocity family `eC`, transported to `F` and to the standalone `E_j`. Then the
conditional pair epsilon value of every admissible bottom-field datum is
`ε(χ₀, ψF, μF, s)^d Π_j (ε(η_j, ψF ∘ Tr, μ_j, s) / ε(η'_j, ψF ∘ Tr, μ_j, s))^{n_j}`, with
`ε = PadicAbelian.epsilon`. Here `ψF` is the additive character of `F` corresponding to the
bottom-field character, `μF` is the measure on `F` corresponding to the bottom-field measure,
and the `μ_j` are arbitrary Haar measures on the `E_j`. -/
theorem conditionalPairEpsilonValue_eq_epsilon_of_virtualIdentity
    (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{u, uE} F)
    (hε : NonabelianSystem.IsSystem F eC ε)
    (V W : LocalWeilRepresentation.{u, uA} F) (T : LocalWeilRepresentation.{u, max u w} F)
    (hT : T.IsContinuous) (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W))
    {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ) (χ₀ : QuasiCharacter F) (d : ℤ)
    (h : ofRepresentation _ ⟨T, hT⟩ =
      d • characterClass.{u, max u w}
        (RankOne.weilCharacter F (baseReciprocityCandidate F eC) χ₀) +
      ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (RankOne.weilCharacter (E j)
            (LocalClassField.extensionReciprocityCandidate F (E j) (g j) eC) (η j)) -
          characterClass.{u, w} (RankOne.weilCharacter (E j)
            (LocalClassField.extensionReciprocityCandidate F (E j) (g j) eC) (η' j))))
    (ψF : NontrivialAdditiveCharacter F) (ψ : AdditiveCharacter F (baseExtension F))
    (hψ : IsBaseCharacter F ψF ψ) (μ : HaarMeasure F (baseExtension F))
    (μE : ∀ j, LocalAdditiveHaarMeasure (E j))
    (A B : CommonClosureWeilDeligne.Pair.{u, uE} F (baseExtension F))
    (hA : IsBaseRestriction F (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom V)) A)
    (hB : IsBaseRestriction F (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom W)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : CommonClosureWeilDeligne.GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ μ A B hAc hBc
        Φ s : ℂ) =
      PadicAbelian.epsilon F.canonicalTopologicalData χ₀ ψF
          ((baseFieldHaarMeasureEquiv F).symm μ).measure s ^ d *
        ∏ j, (PadicAbelian.epsilon (E j).canonicalTopologicalData (η j)
            (standaloneTraceCharacter F (E j) (g j) ψF) (μE j).measure s /
          PadicAbelian.epsilon (E j).canonicalTopologicalData (η' j)
            (standaloneTraceCharacter F (E j) (g j) ψF) (μE j).measure s) ^ n j := by
  rw [conditionalPairEpsilonValue_eq_of_virtualIdentity F eC ε hε V W T hT eT E g _ _ n _ d h ψ μ
    (fun j => CommonClosureSystemTransport.imageHaarMeasure F (E j) (g j) (μE j)) A B hA hB hAc hBc
    Φ s, baseFactor_eq_epsilon F eC hε.1 χ₀ ψF ψ hψ μ s]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [traceCharacter_eq_imageAdditiveCharacter F (E j) (g j) ψF ψ hψ,
    imageFactor_eq_epsilon F (E j) (g j) eC hε.1, imageFactor_eq_epsilon F (E j) (g j) eC hε.1]

end Assembled

end Langlands.Weil.Local.SystemEpsilon
