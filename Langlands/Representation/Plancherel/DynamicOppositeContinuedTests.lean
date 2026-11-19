import Langlands.Representation.Plancherel.ContinuedCompactTestEvaluation
import Langlands.Representation.Plancherel.DynamicOppositeConjugateDomain
import Langlands.Representation.Plancherel.StandardIntertwiningAmbientTwist
import Langlands.Representation.Plancherel.CompactInductionGeneration

/-! # Compact test normalization for the continued actual opposite pair -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.HarmonicAnalysis

namespace Langlands.Plancherel.DynamicOppositeContinuedTests

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily Haar
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open OppositeIntertwiningHermitianAdjunction DynamicOppositeHermitianAdjunctionProof

private theorem weakIntegral_at_one {G : Type u} [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
    {P M U U' : Subgroup G} (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    [MeasurableSpace U'] [BorelSpace U'] [MeasurableSpace (U.subgroupOf U')]
    [BorelSpace (U.subgroupOf U')] [MeasurableSpace (QuotientSpace (U := U) U')]
    [BorelSpace (QuotientSpace (U := U) U')]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {ν : Measure (QuotientSpace (U := U) U')}
    (hbot : U ⊓ U' = ⊥) (hμI : μI Set.univ = 1)
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    (A : SmoothRep.{0, u, uV} ℂ M)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    {Jf : G → A} (hJ : HasIntegral h hU U' A ν f Jf) :
    SmoothWeakIntegral.HasIntegral A.representation μU'
      (fun y : U' => eval P (leviInflatedInducingRepresentation h hU A) f y) (Jf 1) := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let : IsFiniteMeasure μI := ⟨by rw [hμI]; exact ENNReal.one_lt_top⟩
  intro ℓ
  let b := fun q => ℓ.val (integrand h hU U' A 1 f q)
  have hb (y : U') : b (Quotient.mk _ y) = ℓ.val (eval P
      (leviInflatedInducingRepresentation h hU A) f y) := by
    simp only [b, integrand_mk, mul_one]
  have hI : IsClosed ((U.subgroupOf U' : Subgroup U') : Set U') :=
    hU.preimage continuous_subtype_val
  obtain ⟨hf, he⟩ := hJ 1 ℓ
  exact ⟨by simpa only [hb] using
    (integrable_trivialQuotient_iff (U.subgroupOf U') (subgroupOf_eq_one hbot) hI hμI hν b).mp hf,
    by simpa only [hb] using
      (integral_trivialQuotient (U.subgroupOf U') (subgroupOf_eq_one hbot) hI hμI hν b).symm.trans he⟩

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  Langlands.Plancherel.hermitianAdjunctionPointMeasurable
  Langlands.Plancherel.hermitianAdjunctionPointBorel
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace3
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace3
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace4
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace4
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace5
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace5
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace6
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace6

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance oppositeContinuedTestLeviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

local instance oppositeContinuedTestRadicalLocallyCompact : LocallyCompactSpace (radical χ) :=
  (radical_isClosed χ).locallyCompactSpace

local instance oppositeContinuedTestRadicalSecondCountable : SecondCountableTopology (radical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (radical χ : Set (RationalPoint F G.X))

local instance oppositeContinuedTestOppositeRadicalSecondCountable :
    SecondCountableTopology (oppositeRadical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (oppositeRadical χ : Set (RationalPoint F G.X))

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "L" => parameterScheme χ
local notation "hp" => parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "e" => parameterHomeomorph χ
local notation "τ" => parameterTransport χ
set_option quotPrecheck false in
local notation "hcν" => (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
local notation "EP" => unramifiedLeviInductionCompactEquiv
  (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG) K
  (parabolic_isClosed χ) hK hPK (leviNormCharacters χ) hcν (projection_continuous χ)
local notation "EQ" => unramifiedLeviInductionCompactEquiv
  (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG) K
  (oppositeParabolic_isClosed χ) hK hOppK (leviNormCharacters χ) hcν
  (oppositeProjection_continuous χ)
local notation "IP" => UnramifiedLeviInduction
  (decomposition χ) (radical_isClosed χ) (leviNormCharacters χ)
local notation "IQ" => UnramifiedLeviInduction
  (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (leviNormCharacters χ)

set_option maxHeartbeats 600000

section Forward

variable (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ forwardFullDomainRegion χ K hK A)

local notation "J" => conditionalForwardFamily χ K hK hRefl hCST hG A
local notation "continueActual" => continuedInductionIntertwiner L hp hL
  (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
  (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG) K hK
  (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
  (projection_continuous χ) (oppositeProjection_continuous χ) e (normCharacters_continuous χ) A
  J p hD hne hDΩ

/-- The actual ambient forward continuation underlying the canonical scalar. -/
def forwardIntertwiner (z : p.regularRegion) :
    (IP (τ z.val) A).representation.IntertwiningMap (IQ (τ z.val) A).representation :=
  continueActual z

local notation "Jc" => forwardIntertwiner χ hRefl hCST hG K hK hPK hOppK A p hD hne hDΩ
local notation "ρtest" => oppositeRadicalHaar χ K hK
local notation "evaluation" => compactEvalLinear (oppositeDecomposition χ) K A 1

/-- At a regular parameter, the forward continuation agrees with integration
on every section compactly supported on the target radical. -/
theorem forwardIntertwiner_compactTest (z : p.regularRegion) (f : IP (τ z.val) A)
    (hf : HasCompactSupport (fun y : oppositeRadical χ => eval _ _ f y.val)) (ℓ : A →ₗ[ℂ] ℂ) :
    Integrable (fun y : oppositeRadical χ => ℓ (eval _ _ f y.val)) ρtest ∧
      ℓ (eval _ _ (Jc z f) 1) = ∫ y : oppositeRadical χ, ℓ (eval _ _ f y.val) ∂ρtest := by
  let f₀ := EP (τ z.val) A f
  let B := compactTestSectionValues L (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (projection_continuous χ)
    e (normCharacters_continuous χ) A f₀ (Subtype.val : oppositeRadical χ → _)
  have hf₀ : (EP (τ z.val) A).symm f₀ = f :=
    LinearEquiv.symm_apply_apply _ f
  have hsource : (fun y : oppositeRadical χ => B y z.val) = fun y => eval _ _ f y.val :=
    funext fun y => congrArg (fun f' : IP (τ z.val) A => eval _ _ f' y.val) hf₀
  have support : HasCompactSupport (fun y => B y z.val) := hsource.symm ▸ hf
  have start (w : D) : SmoothWeakIntegral.HasIntegral A.representation ρtest
      (fun y => B y w.val) (evaluation (conditionalForwardCompactFamily
        χ hRefl hCST hG K hK hPK hOppK A ⟨w.val, hDΩ w.property⟩ f₀)) := by
    let w' : forwardFullDomainRegion χ K hK A := ⟨w.val, hDΩ w.property⟩
    let fw := (EP (τ w.val) A).symm f₀
    have hj := conditionalForwardFamily_spec χ K hK hRefl hCST hG A w' fw
    have hv := weakIntegral_at_one (decomposition χ) (radical_isClosed χ) (oppositeRadical_isClosed χ)
      (radical_inf_oppositeRadical χ)
      (sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ))
      (forwardQuotientMeasure_isCompatible χ K hK) _ fw hj
    exact (SmoothWeakIntegral.hasIntegral_twist_iff A.representation ρtest
      (τ w.val).val.toMonoidHom (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
        (τ w.val))).mp hv
  have H := continuedOperator_compactTest_integral L (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (projection_continuous χ)
    e (normCharacters_continuous χ) A f₀ (Subtype.val : oppositeRadical χ → _) ρtest hp hL p evaluation
    continuous_subtype_val z.val support (compactOpenCofinal_of_nonarchimedean (levi χ))
    hD hne hDΩ start z ℓ
  have he := continuedInductionIntertwiner_compact L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ) e (normCharacters_continuous χ) A
    J p hD hne hDΩ z
  have hEval : evaluation (p.continuedOperator z f₀) = eval _ _ (Jc z f) 1 := by
    calc
      _ = eval _ _ (Jc z ((EP (τ z.val) A).symm f₀)) 1 :=
        congrArg (fun T : CompactInductionPicture (decomposition χ) K A →ₗ[ℂ]
          CompactInductionPicture (oppositeDecomposition χ) K A => evaluation (T f₀)) he.symm
      _ = _ := congrArg (fun f' : IP (τ z.val) A => eval _ _ (Jc z f') 1) hf₀
  have htest : (fun y : oppositeRadical χ => ℓ (B y z.val)) = fun y => ℓ (eval _ _ f y.val) :=
    congrArg (fun g : oppositeRadical χ → A => ℓ ∘ g) hsource
  refine ⟨htest ▸ H.1, (congrArg ℓ hEval.symm).trans (H.2.trans ?_)⟩
  exact congrArg (fun g : oppositeRadical χ → ℂ => ∫ y, g y ∂ρtest) htest

end Forward

section Reverse

variable (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ reverseFullDomainRegion χ K hK A)

local notation "J" => conditionalReverseFamily χ K hK hRefl hCST hG A
local notation "continueActual" => continuedInductionIntertwiner L hp hL
  (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG)
  (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG) K hK
  (oppositeParabolic_isClosed χ) (parabolic_isClosed χ) hOppK hPK
  (oppositeProjection_continuous χ) (projection_continuous χ) e (normCharacters_continuous χ) A
  J q hD hne hDΩ

/-- The actual ambient reverse continuation underlying the canonical scalar. -/
def reverseIntertwiner (z : q.regularRegion) :
    (IQ (τ z.val) A).representation.IntertwiningMap (IP (τ z.val) A).representation :=
  continueActual z

local notation "Jc" => reverseIntertwiner χ hRefl hCST hG K hK hPK hOppK A q hD hne hDΩ
local notation "ρtest" => radicalHaar χ K hK
local notation "evaluation" => compactEvalLinear (decomposition χ) K A 1

/-- At a regular parameter, the reverse continuation agrees with integration
on every section compactly supported on the target radical. -/
theorem reverseIntertwiner_compactTest (z : q.regularRegion) (f : IQ (τ z.val) A)
    (hf : HasCompactSupport (fun y : radical χ => eval _ _ f y.val)) (ℓ : A →ₗ[ℂ] ℂ) :
    Integrable (fun y : radical χ => ℓ (eval _ _ f y.val)) ρtest ∧
      ℓ (eval _ _ (Jc z f) 1) = ∫ y : radical χ, ℓ (eval _ _ f y.val) ∂ρtest := by
  let f₀ := EQ (τ z.val) A f
  let B := compactTestSectionValues L (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K (oppositeParabolic_isClosed χ) hK hOppK (oppositeProjection_continuous χ)
    e (normCharacters_continuous χ) A f₀ (Subtype.val : radical χ → _)
  have hf₀ : (EQ (τ z.val) A).symm f₀ = f :=
    LinearEquiv.symm_apply_apply _ f
  have hsource : (fun y : radical χ => B y z.val) = fun y => eval _ _ f y.val :=
    funext fun y => congrArg (fun f' : IQ (τ z.val) A => eval _ _ f' y.val) hf₀
  have support : HasCompactSupport (fun y => B y z.val) := hsource.symm ▸ hf
  have start (w : D) : SmoothWeakIntegral.HasIntegral A.representation ρtest
      (fun y => B y w.val) (evaluation (conditionalReverseCompactFamily
        χ hRefl hCST hG K hK hPK hOppK A ⟨w.val, hDΩ w.property⟩ f₀)) := by
    let w' : reverseFullDomainRegion χ K hK A := ⟨w.val, hDΩ w.property⟩
    let fw := (EQ (τ w.val) A).symm f₀
    have hj := conditionalReverseFamily_spec χ K hK hRefl hCST hG A w' fw
    have hv := weakIntegral_at_one (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (radical_isClosed χ)
      ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)) (sourceIntersectionHaar_univ K hK _ _ _ _ ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)))
      (reverseQuotientMeasure_isCompatible χ K hK) _ fw hj
    exact (SmoothWeakIntegral.hasIntegral_twist_iff A.representation ρtest
      (τ w.val).val.toMonoidHom (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
        (τ w.val))).mp hv
  have H := continuedOperator_compactTest_integral L (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K (oppositeParabolic_isClosed χ) hK hOppK (oppositeProjection_continuous χ)
    e (normCharacters_continuous χ) A f₀ (Subtype.val : radical χ → _) ρtest hp hL q evaluation
    continuous_subtype_val z.val support (compactOpenCofinal_of_nonarchimedean (levi χ))
    hD hne hDΩ start z ℓ
  have he := continuedInductionIntertwiner_compact L hp hL
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG)
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG) K hK
    (oppositeParabolic_isClosed χ) (parabolic_isClosed χ) hOppK hPK
    (oppositeProjection_continuous χ) (projection_continuous χ) e (normCharacters_continuous χ) A
    J q hD hne hDΩ z
  have hEval : evaluation (q.continuedOperator z f₀) = eval _ _ (Jc z f) 1 := by
    calc
      _ = eval _ _ (Jc z ((EQ (τ z.val) A).symm f₀)) 1 :=
        congrArg (fun T : CompactInductionPicture (oppositeDecomposition χ) K A →ₗ[ℂ]
          CompactInductionPicture (decomposition χ) K A => evaluation (T f₀)) he.symm
      _ = _ := congrArg (fun f' : IQ (τ z.val) A => eval _ _ (Jc z f') 1) hf₀
  have htest : (fun y : radical χ => ℓ (B y z.val)) = fun y => ℓ (eval _ _ f y.val) :=
    congrArg (fun g : radical χ → A => ℓ ∘ g) hsource
  refine ⟨htest ▸ H.1, (congrArg ℓ hEval.symm).trans (H.2.trans ?_)⟩
  exact congrArg (fun g : radical χ → ℂ => ∫ y, g y ∂ρtest) htest

end Reverse

end Langlands.Plancherel.DynamicOppositeContinuedTests
