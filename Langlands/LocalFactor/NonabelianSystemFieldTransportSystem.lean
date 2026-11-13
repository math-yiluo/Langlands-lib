import Langlands.LocalFactor.NonabelianSystemFieldTransportReciprocity
import Langlands.LocalFactor.NonabelianSystem
import Langlands.LocalFactor.Abelian.Transport

/-!
# Local-constant systems along an isomorphism of p-adic fields

For `g : F ≅ E` over `ℚ_p` and an assignment `ε` on the common closure of `E`, the
transported assignment on `F` evaluates `ε` at `σ(L)` on the transported additive
character, the pushed-forward Haar measure and the transported virtual class.
-/

noncomputable section

universe u u₁ u₂ uV

namespace Langlands.LocalFactor.NonabelianSystem.FieldTransport

open LocalClassField Weil.Local CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u₁} p) (E : PadicField.{u₂} p)
  (g : F.Carrier ≃ₐ[Padic p] E.Carrier)

attribute [local instance] extensionTopology

section Scale

variable (A : PadicField.{u₁} p) (B : PadicField.{u₂} p) (e : A.Carrier ≃ₐ[Padic p] B.Carrier)

local instance : TopologicalSpace A.Carrier := A.canonicalTopologicalData.topology
local instance : TopologicalSpace B.Carrier := B.canonicalTopologicalData.topology
local instance : MeasurableSpace A.Carrier := borel A.Carrier
local instance : MeasurableSpace B.Carrier := borel B.Carrier
local instance : BorelSpace A.Carrier := ⟨rfl⟩
local instance : BorelSpace B.Carrier := ⟨rfl⟩
local instance : IsTopologicalRing A.Carrier := by
  let := A.canonicalTopologicalData.valuativeRel
  let := A.canonicalTopologicalData.localField
  infer_instance
local instance : IsTopologicalRing B.Carrier := by
  let := B.canonicalTopologicalData.valuativeRel
  let := B.canonicalTopologicalData.localField
  infer_instance

/-- Pushforward along a field isomorphism commutes with positive scaling. -/
theorem _root_.Langlands.PadicField.AbelianTransport.haarMeasure_scale
    (μ : HarmonicAnalysis.AdditiveHaarMeasure A.Carrier) (c : NNReal) (hc : 0 < c) :
    PadicField.AbelianTransport.haarMeasure A B e (μ.scale c hc) =
      (PadicField.AbelianTransport.haarMeasure A B e μ).scale c hc :=
  HarmonicAnalysis.FieldTransport.haarMeasure_scale _ _ _ μ c hc

end Scale

/-- The additive character of `σ(L)` transported from `L`. -/
def additiveCharacterMap (L : Extension F) (ψ : AdditiveCharacter F L) :
    AdditiveCharacter E (mapExtension F E g L) :=
  PadicField.ConductorTransport.additiveCharacter (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L) ψ

/-- The Haar measure of `σ(L)` pushed forward from `L`. -/
def haarMeasureMap (L : Extension F) (μ : HaarMeasure F L) :
    HaarMeasure E (mapExtension F E g L) :=
  PadicField.AbelianTransport.haarMeasure (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L) μ

/-- The local-constant assignment on `F` transported from one on `E`. -/
def transportAssignment (ε : Assignment.{u₂, uV} E) : Assignment.{u₁, uV} F :=
  fun L ψ μ x => ε (mapExtension F E g L) (additiveCharacterMap F E g L ψ)
    (haarMeasureMap F E g L μ) (virtualMap F E g L x)

theorem transportAssignment_apply (ε : Assignment.{u₂, uV} E) (L : Extension F)
    (ψ : AdditiveCharacter F L) (μ : HaarMeasure F L) (x : Virtual.{u₁, uV} F L) :
    transportAssignment F E g ε L ψ μ x = ε (mapExtension F E g L)
      (additiveCharacterMap F E g L ψ) (haarMeasureMap F E g L μ) (virtualMap F E g L x) :=
  rfl

theorem additiveRelation_transportAssignment {ε : Assignment.{u₂, uV} E}
    (hε : AdditiveRelation E ε) : AdditiveRelation F (transportAssignment F E g ε) := by
  intro L ψ μ x y
  rw [transportAssignment_apply, transportAssignment_apply, transportAssignment_apply, map_add]
  exact hε _ _ _ _ _

theorem haarMeasureMap_scaleHaar (L : Extension F) (μ : HaarMeasure F L) (c : NNReal)
    (hc : 0 < c) :
    haarMeasureMap F E g L (scaleHaar F L μ c hc) =
      scaleHaar E (mapExtension F E g L) (haarMeasureMap F E g L μ) c hc :=
  PadicField.AbelianTransport.haarMeasure_scale _ _ (fieldEquiv F E g L) μ c hc

theorem haarScalingRelation_transportAssignment {ε : Assignment.{u₂, uV} E}
    (hε : HaarScalingRelation E ε) : HaarScalingRelation F (transportAssignment F E g ε) := by
  intro L ψ μ c hc x
  rw [transportAssignment_apply, transportAssignment_apply, haarMeasureMap_scaleHaar,
    hε, degree_virtualMap]

theorem additiveCharacterMap_apply (L : Extension F) (ψ : AdditiveCharacter F L)
    (y : (mapExtension F E g L).field) :
    additiveCharacterMap F E g L ψ y = ψ ((mapFieldRingEquiv F E g L).symm y) := rfl

/-- The field trace commutes with `L ≅ σ(L)`. -/
theorem mapFieldRingEquiv_symm_trace {M L : Extension F} (h : M.field ≤ L.field)
    (y : (mapExtension F E g L).field) :
    letI : Algebra M.field L.field := (IntermediateField.inclusion h).toAlgebra
    letI : Algebra (mapExtension F E g M).field (mapExtension F E g L).field :=
      (IntermediateField.inclusion (mapExtension_mono F E g h)).toAlgebra
    (mapFieldRingEquiv F E g M).symm (Algebra.trace (mapExtension F E g M).field
        (mapExtension F E g L).field y) =
      Algebra.trace M.field L.field ((mapFieldRingEquiv F E g L).symm y) := by
  let : Algebra M.field L.field := (IntermediateField.inclusion h).toAlgebra
  let : Algebra (mapExtension F E g M).field (mapExtension F E g L).field :=
    (IntermediateField.inclusion (mapExtension_mono F E g h)).toAlgebra
  rw [Algebra.trace_eq_of_equiv_equiv (mapFieldRingEquiv F E g M) (mapFieldRingEquiv F E g L)
    (fieldEquiv_algebraMap_comp F E g h) ((mapFieldRingEquiv F E g L).symm y),
    RingEquiv.apply_symm_apply]

/-- The trace character commutes with the transport of additive characters. -/
theorem traceCharacter_additiveCharacterMap {M L : Extension F} (h : M.field ≤ L.field)
    (ψ : AdditiveCharacter F M) :
    traceCharacter E (mapExtension F E g M) (mapExtension F E g L) (mapExtension_mono F E g h)
        (additiveCharacterMap F E g M ψ) =
      additiveCharacterMap F E g L (traceCharacter F M L h ψ) := by
  let := (canonicalData E (mapExtension F E g L)).topology
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro y
  rw [traceCharacter_apply, additiveCharacterMap_apply, additiveCharacterMap_apply,
    traceCharacter_apply]
  exact congrArg ψ (mapFieldRingEquiv_symm_trace F E g h y)

theorem inductionRelation_transportAssignment {ε : Assignment.{u₂, uV} E}
    (hε : InductionRelation E ε) : InductionRelation F (transportAssignment F E g ε) := by
  intro M L h ψ μ μL x
  have hx : virtualMap F E g L x.val ∈ DegreeZero.{u₂, uV} E (mapExtension F E g L) := by
    rw [ExactGrothendieckGroup.mem_degreeZero]
    change degree E (mapExtension F E g L) (virtualMap F E g L x.val) = 0
    rw [degree_virtualMap]
    exact (ExactGrothendieckGroup.mem_degreeZero _ x.val).mp x.property
  rw [transportAssignment_apply, transportAssignment_apply, virtualMap_induce,
    ← traceCharacter_additiveCharacterMap]
  exact hε (mapExtension F E g M) (mapExtension F E g L) (mapExtension_mono F E g h)
    (additiveCharacterMap F E g M ψ) (haarMeasureMap F E g M μ) (haarMeasureMap F E g L μL)
    ⟨_, hx⟩

/-- The field character of `σ(L)` transported from `L`: `χ ∘ (L ≅ σ(L))⁻¹` on units. -/
def fieldCharacterMap (L : Extension F) (χ : FieldCharacter F L) :
    FieldCharacter E (mapExtension F E g L) :=
  PadicField.ConductorTransport.quasicharacter (L.asPadicField (p := p))
    ((mapExtension F E g L).asPadicField (p := p)) (fieldEquiv F E g L) χ

/-- Pulled back to `W_E(σ(L))`, the transported family's Weil character of `χ` is the
Weil character of the transported field character. -/
theorem weilCharacter_transportFamily (eE : ReciprocityFamily E) (L : Extension F)
    (χ : FieldCharacter F L) :
    (weilCharacter F (transportFamily F E g eE) L χ).comp
        (subgroupWeilEquiv F E g L : _ →ₜ* weilSubgroup F L) =
      weilCharacter E eE (mapExtension F E g L) (fieldCharacterMap F E g L χ) := by
  ext w
  change ((χ (transportFamily F E g eE L (abelianizationProjection _
      (subgroupWeilEquiv F E g L w))) : ℂˣ) : ℂ) =
    ((χ ((unitsEquiv F E g L).symm (eE (mapExtension F E g L)
      (abelianizationProjection _ w))) : ℂˣ) : ℂ)
  rw [transportFamily_apply, LocalClassField.abelianizationCongr_symm,
    LocalClassField.abelianizationCongr_projection,
    ContinuousMulEquiv.symm_apply_apply]

theorem virtualMap_characterClass_transportFamily (eE : ReciprocityFamily E) (L : Extension F)
    (χ : FieldCharacter F L) :
    virtualMap F E g L (characterClass.{u₁, uV} F (transportFamily F E g eE) L χ) =
      characterClass.{u₂, uV} E eE (mapExtension F E g L) (fieldCharacterMap F E g L χ) := by
  rw [characterClass, virtualMap_characterClass, weilCharacter_transportFamily]
  rfl

theorem rankOneRelation_transportAssignment {eE : ReciprocityFamily E}
    {ε : Assignment.{u₂, uV} E} (hε : RankOneRelation E eE ε) :
    RankOneRelation F (transportFamily F E g eE) (transportAssignment F E g ε) := by
  intro L χ ψ μ
  rw [transportAssignment_apply, virtualMap_characterClass_transportFamily]
  refine (hε (mapExtension F E g L) (fieldCharacterMap F E g L χ)
    (additiveCharacterMap F E g L ψ) (haarMeasureMap F E g L μ)).trans ?_
  exact PadicField.AbelianTransport.abelianEpsilonExpression_eq _ _ (fieldEquiv F E g L) χ ψ μ

/-- The transport of a local-constant system for a normalized family is a local-constant
system for the transported family. -/
theorem isSystem_transportAssignment {eE : ReciprocityFamily E} {ε : Assignment.{u₂, uV} E}
    (hε : IsSystem E eE ε) :
    IsSystem F (transportFamily F E g eE) (transportAssignment F E g ε) :=
  ⟨transportFamily_normalizedReciprocity F E g eE hε.1,
    additiveRelation_transportAssignment F E g hε.2.1,
    haarScalingRelation_transportAssignment F E g hε.2.2.1,
    inductionRelation_transportAssignment F E g hε.2.2.2.1,
    rankOneRelation_transportAssignment F E g hε.2.2.2.2⟩

end Langlands.LocalFactor.NonabelianSystem.FieldTransport
