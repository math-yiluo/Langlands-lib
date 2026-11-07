import Langlands.Representation.Plancherel.ContinuedInductionOrbitScalar
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Original self-comparisons for the actual standard integral families -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uH uG uI uV uW

section FullDomainRegion

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (U' : Subgroup G) (e : H ≃ₜ* M)
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

local notation "νM" =>
  (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν

/-- Parameters where every actual source vector has absolutely convergent
smooth-dual scalar integrals represented in the original inducing carrier. -/
def standardIntertwiningFullDomainRegion (A : SmoothRep.{0, uG, uV} ℂ M) :
    Set (unramifiedCharacters ν) :=
  {χ | domain h hU U'
    (A.twist (χM χ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM χ))) qν = ⊤}

/-- The full integral region transports exactly under an actual twisting
equivalence, with the quotient measure unchanged. -/
theorem standardIntertwiningFullDomainRegion_translation_iff
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation) :
    τ * χ ∈ standardIntertwiningFullDomainRegion h hU U' e ν qν A ↔
      χ ∈ standardIntertwiningFullDomainRegion h hU U' e ν qν B :=
  domain_eq_top_iff_equiv h hU U' qν (transportedBaseTwistEquiv e ν τ χ a)

/-- In particular an actual self-twist preserves the entire full-domain
region. Its openness or nonemptiness is not asserted. -/
theorem standardIntertwiningFullDomainRegion_self_translation
    (A : SmoothRep.{0, uG, uV} ℂ M) (τ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv A.representation) :
    (unramifiedParameterTranslation ν τ) ⁻¹'
        standardIntertwiningFullDomainRegion h hU U' e ν qν A =
      standardIntertwiningFullDomainRegion h hU U' e ν qν A := by
  apply Set.ext
  intro χ
  change (unramifiedParameterTranslation ν τ χ ∈
    standardIntertwiningFullDomainRegion h hU U' e ν qν A) ↔ _
  rw [unramifiedParameterTranslation_apply]
  exact standardIntertwiningFullDomainRegion_translation_iff h hU U' e ν qν τ χ a

variable {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The original standard integral family on its actual full-domain
parameter region, valued in ambient normalized-induction intertwining maps. -/
def standardInductionIntertwinerFamily (A : SmoothRep.{0, uG, uV} ℂ M)
    (χ : standardIntertwiningFullDomainRegion h hU U' e ν qν A) :
    (UnramifiedLeviInduction h hU νM (χM χ.val) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' νM (χM χ.val) A).representation :=
  fullSourceIntertwiner h hU h' hU'
    (A.twist (χM χ.val).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM χ.val)))
    qν μU' μI hqν hM hsq χ.property

/-- Every value of the family satisfies the original smooth-dual scalar
integral relation at every source input and every ambient group element. -/
theorem standardInductionIntertwinerFamily_spec
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (χ : standardIntertwiningFullDomainRegion h hU U' e ν qν A)
    (f : UnramifiedLeviInduction h hU νM (χM χ.val) A) :
    HasIntegral h hU U'
      (A.twist (χM χ.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (χM χ.val))) qν f
      (eval P' (leviInflatedInducingRepresentation h' hU'
          (A.twist (χM χ.val).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker νM (χM χ.val))))
        (standardInductionIntertwinerFamily
          h hU U' e ν qν h' hU' μU' μI hqν hM hsq A χ f)) :=
  fullSourceIntertwiner_spec h hU h' hU' _ qν μU' μI hqν hM hsq χ.property f

/-- Original naturality is proved for these standard families, including
the translated full-domain membership. It is not a supplied comparison square. -/
theorem standardInductionIntertwinerFamily_natural
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv B.representation)
    (hχ : χ ∈ standardIntertwiningFullDomainRegion h hU U' e ν qν B)
    (f : UnramifiedLeviInduction h hU νM (χM (τ * χ)) A) :
    standardInductionIntertwinerFamily h hU U' e ν qν h' hU' μU' μI hqν hM hsq B
        ⟨χ, hχ⟩
        (inducedMap h hU (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap f) =
      inducedMap h' hU' (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap
        (standardInductionIntertwinerFamily h hU U' e ν qν h' hU' μU' μI
          hqν hM hsq A
          ⟨τ * χ, (standardIntertwiningFullDomainRegion_translation_iff
            h hU U' e ν qν τ χ a).mpr hχ⟩ f) := by
  exact congrArg (fun T => T f)
    (fullSourceIntertwiner_natural h hU h' hU' qν μU' μI hqν hM hsq
      ((standardIntertwiningFullDomainRegion_translation_iff
        h hU U' e ν qν τ χ a).mpr hχ) hχ
      (transportedBaseTwistEquiv e ν τ χ a).toIntertwiningMap)

end FullDomainRegion

section SelfComparison

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (e : H ≃ₜ* M) {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  (A : SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace U₀] [BorelSpace U₀]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₀)] [BorelSpace (U₁.subgroupOf U₀)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₀)]
  [BorelSpace (QuotientSpace (U := U₁) U₀)]
  (q₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (q₀₁ : Measure (QuotientSpace (U := U₁) U₀))
  (μU₀ : Measure U₀) (μU₁ : Measure U₁)
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₀₁ : Measure (U₁.subgroupOf U₀))
  [IsHaarMeasure μU₀] [μU₀.Regular] [IsMulRightInvariant μU₀]
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μI₀₁] [μI₀₁.Regular] [IsMulRightInvariant μI₀₁]
  (hq₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ q₁₀)
  (hq₀₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₀) μU₀ μI₀₁ q₀₁)
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
  (hsq₀₁ : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)

local notation "νM" =>
  (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν
local notation "Ω₁₀" => standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e ν q₁₀ A
local notation "Ω₀₁" => standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e ν q₀₁ A
local notation "J₁₀" => standardInductionIntertwinerFamily
  h₀ hU₀ U₁ e ν q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A
local notation "J₀₁" => standardInductionIntertwinerFamily
  h₁ hU₁ U₀ e ν q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A

variable {D₁₀ D₀₁ : Set (unramifiedCharacters ν)}
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty)
  (hD₁₀Ω : D₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e ν q₁₀ A)
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty)
  (hD₀₁Ω : D₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e ν q₀₁ A)

/-- Full convergence on separate nonempty ambient opens supplies the actual
standard-integral self-comparison data for every genuine inducing self-twist. -/
def standardInductionSelfBaseChangeData (τ : unramifiedCharacters ν)
    (a : (A.twist (χM τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker νM (χM τ))).representation.Equiv A.representation) :
    InductionSelfBaseChangeData h₀ hU₀ h₁ hU₁ e ν A J₁₀ J₀₁ τ where
  twistEquiv := a
  forwardRegion := D₁₀
  reverseRegion := D₀₁
  forward_isOpen := hD₁₀
  forward_nonempty := hne₁₀
  forward_in_translation χ hχ :=
    (standardIntertwiningFullDomainRegion_translation_iff
      h₀ hU₀ U₁ e ν q₁₀ τ χ a).mpr (hD₁₀Ω hχ)
  forward_in_original := hD₁₀Ω
  reverse_isOpen := hD₀₁
  reverse_nonempty := hne₀₁
  reverse_in_translation χ hχ :=
    (standardIntertwiningFullDomainRegion_translation_iff
      h₁ hU₁ U₀ e ν q₀₁ τ χ a).mpr (hD₀₁Ω hχ)
  reverse_in_original := hD₀₁Ω
  forward_natural χ hχ f :=
    standardInductionIntertwinerFamily_natural
      h₀ hU₀ U₁ e ν q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ τ χ a (hD₁₀Ω hχ) f
  reverse_natural χ hχ f :=
    standardInductionIntertwinerFamily_natural
      h₁ hU₁ U₀ e ν q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ τ χ a (hD₀₁Ω hχ) f

variable [NonarchimedeanGroup H]

include hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω in
/-- Every element of the full actual inducing twist stabilizer supplies
the original standard-integral self-comparison witness required for descent. -/
theorem standardInductionSelfBaseChangeData_stabilizer :
    ∀ τ : smoothRepUnramifiedTwistStabilizer ν (SmoothRep.pullback e A),
      Nonempty (InductionSelfBaseChangeData h₀ hU₀ h₁ hU₁ e ν A J₁₀ J₀₁ τ.val) := by
  intro τ
  exact ⟨standardInductionSelfBaseChangeData
    h₀ hU₀ h₁ hU₁ e ν A q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω τ.val
    (stabilizerBaseTwistEquiv e ν τ)⟩

end SelfComparison

end Langlands.Plancherel
