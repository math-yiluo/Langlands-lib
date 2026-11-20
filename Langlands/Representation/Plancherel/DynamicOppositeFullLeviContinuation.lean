import Langlands.Representation.Plancherel.StandardLeviPlancherelWeightFullRoot
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviInduction

/-! # Full domains, continuations and irreducibility for a central cocharacter

When the centralizer of the cocharacter `χ` is all of `G(F)`, both radicals of the actual
opposite pair are trivial. Then:

* the standard integrals converge for every vector and every unramified parameter, so the
  forward and reverse full domains are all unramified characters
  (`forwardFullDomainRegion_eq_univ_of_levi_eq_top`,
  `reverseFullDomainRegion_eq_univ_of_levi_eq_top`);
* the compact-picture integrals do not depend on the parameter, so they admit continuation data
  with denominator `1` and a constant numerator (`forwardContinuationOfLeviEqTop`,
  `reverseContinuationOfLeviEqTop`);
* the Levi-normalized induction at every parameter is the twisted representation itself, so it is
  irreducible when the inducing representation is
  (`unramifiedLeviInduction_isIrreducible_of_levi_eq_top`).
-/

noncomputable section

universe u uG uH uI uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Standard integrals over a trivial radical always converge -/

section TrivialRadicalDomain

open Aubert.General Induction StandardIntertwining
open OppositeIntertwiningHermitianAdjunction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) {U' : Subgroup G}
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]

/-- **Over a trivial radical, evaluation represents the standard integral.** If `U' = 1` and the
Haar measures on `U'` and on `U ∩ U'` give these trivial groups mass one, then for every vector
`f` of the Levi-normalized induction the integral of `u' ↦ f(u' g)` over the compatible quotient
`(U ∩ U') \ U'` converges against every smooth functional and is represented by `f(g)`. -/
theorem hasIntegral_eval_of_eq_bot (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular]
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {qν : Measure (QuotientSpace (U := U) U')}
    (hbot : U' = ⊥) (hμU' : μU' Set.univ = 1) (hμI : μI Set.univ = 1)
    (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    HasIntegral h hU U' A qν f (eval P (leviInflatedInducingRepresentation h hU A) f) := by
  subst hbot
  have hU' : IsClosed (((⊥ : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have : LocallyCompactSpace (⊥ : Subgroup G) := hU'.locallyCompactSpace
  have : IsFiniteMeasure μI := ⟨by rw [hμI]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure μU' := ⟨by rw [hμU']; exact ENNReal.one_lt_top⟩
  have hone : ∀ u' : (⊥ : Subgroup G), u' = 1 := fun u' =>
    Subtype.ext (Subgroup.mem_bot.mp u'.property)
  have hbot' := subgroupOf_eq_one (A := U) (B := (⊥ : Subgroup G)) (by rw [inf_bot_eq])
  have hH : IsClosed ((U.subgroupOf ⊥ : Subgroup (⊥ : Subgroup G)) : Set (⊥ : Subgroup G)) :=
    hU.preimage continuous_subtype_val
  intro g ℓ
  have hfun : (fun u' : (⊥ : Subgroup G) => ℓ.val (integrand h hU ⊥ A g f (Quotient.mk _ u'))) =
      fun _ => ℓ.val (eval P (leviInflatedInducingRepresentation h hU A) f g) := by
    funext u'
    rw [integrand_mk, hone u']
    simp
  refine ⟨(integrable_trivialQuotient_iff (U.subgroupOf ⊥) hbot' hH hμI hqν _).mpr ?_, ?_⟩
  · rw [hfun]
    exact integrable_const _
  · rw [integral_trivialQuotient (U.subgroupOf ⊥) hbot' hH hμI hqν
      (fun q => ℓ.val (integrand h hU ⊥ A g f q)), hfun, integral_const]
    simp [Measure.real, hμU']

/-- Over a trivial radical with mass-one Haar measures, the domain of the standard integral is
the whole Levi-normalized induction. -/
theorem domain_eq_top_of_eq_bot (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular]
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {qν : Measure (QuotientSpace (U := U) U')}
    (hbot : U' = ⊥) (hμU' : μU' Set.univ = 1) (hμI : μI Set.univ = 1)
    (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν) :
    domain h hU U' A qν = ⊤ :=
  eq_top_iff.mpr fun f _ => (mem_domain h hU U' A qν f).mpr
    ⟨_, hasIntegral_eval_of_eq_bot h hU A hbot hμU' hμI hqν f⟩

/-- Over a trivial radical with mass-one Haar measures, the full domain region of the standard
integral is the set of all unramified characters. -/
theorem standardIntertwiningFullDomainRegion_eq_univ_of_eq_bot
    {H : Type uH} [Group H] [TopologicalSpace H] (e : H ≃ₜ* M)
    {I : Type uI} (ν : I → (H →* ℝ≥0ˣ)) (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular]
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {qν : Measure (QuotientSpace (U := U) U')}
    (hbot : U' = ⊥) (hμU' : μU' Set.univ = 1) (hμI : μI Set.univ = 1)
    (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν) :
    standardIntertwiningFullDomainRegion h hU U' e ν qν A = Set.univ :=
  Set.eq_univ_of_forall fun _ => domain_eq_top_of_eq_bot h hU _ hbot hμU' hμI hqν

end TrivialRadicalDomain

/-! ### The actual opposite pair of a central cocharacter -/

section DynamicFullLevi

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open OppositeIntertwiningHermitianAdjunction

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
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-! #### Full domains -/

/-- **The forward full domain of a central cocharacter is everything.** If the centralizer of `χ`
is all of `G(F)`, the actual forward standard integrals converge, at the intrinsic source Haar
scale `K`, for every vector and every unramified parameter. -/
theorem forwardFullDomainRegion_eq_univ_of_levi_eq_top (hlevi : levi χ = ⊤) :
    forwardFullDomainRegion χ K hK A = Set.univ :=
  standardIntertwiningFullDomainRegion_eq_univ_of_eq_bot (decomposition χ) (radical_isClosed χ)
    (parameterHomeomorph χ) (normCharacters χ) A
    (oppositeRadical_eq_bot_of_levi_eq_top χ hlevi)
    (subgroupCompactOpenHaar_univ_of_eq_bot K hK _ _
      (oppositeRadical_eq_bot_of_levi_eq_top χ hlevi))
    (sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ))
    (forwardQuotientMeasure_isCompatible χ K hK)

/-- **The reverse full domain of a central cocharacter is everything.** -/
theorem reverseFullDomainRegion_eq_univ_of_levi_eq_top (hlevi : levi χ = ⊤) :
    reverseFullDomainRegion χ K hK A = Set.univ :=
  standardIntertwiningFullDomainRegion_eq_univ_of_eq_bot (oppositeDecomposition χ)
    (oppositeRadical_isClosed χ) (parameterHomeomorph χ) (normCharacters χ) A
    (radical_eq_bot_of_levi_eq_top χ hlevi)
    (subgroupCompactOpenHaar_univ_of_eq_bot K hK _ _ (radical_eq_bot_of_levi_eq_top χ hlevi))
    (sourceIntersectionHaar_univ K hK _ _ _ _
      ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)))
    (reverseQuotientMeasure_isCompatible χ K hK)

theorem mem_forwardFullDomainRegion_of_levi_eq_top (hlevi : levi χ = ⊤)
    (z : unramifiedCharacters (normCharacters χ)) : z ∈ forwardFullDomainRegion χ K hK A := by
  rw [forwardFullDomainRegion_eq_univ_of_levi_eq_top χ K hK A hlevi]
  exact Set.mem_univ z

theorem mem_reverseFullDomainRegion_of_levi_eq_top (hlevi : levi χ = ⊤)
    (z : unramifiedCharacters (normCharacters χ)) : z ∈ reverseFullDomainRegion χ K hK A := by
  rw [reverseFullDomainRegion_eq_univ_of_levi_eq_top χ K hK A hlevi]
  exact Set.mem_univ z

/-! #### Continuation data with denominator one -/

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

/-- For a central cocharacter, the forward compact-picture integral does not depend on the
parameter. -/
theorem conditionalForwardCompactFamily_eq_of_levi_eq_top (hlevi : levi χ = ⊤)
    (z w : forwardFullDomainRegion χ K hK A) :
    conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z =
      conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A w := by
  refine LinearMap.ext fun φ => compactPictureValues_injective (oppositeDecomposition χ) K A ?_
  rw [conditionalForwardCompactFamily_values_of_levi_eq_top χ hRefl hCST hG K hK hPK hOppK A
      hlevi z φ,
    conditionalForwardCompactFamily_values_of_levi_eq_top χ hRefl hCST hG K hK hPK hOppK A
      hlevi w φ]

/-- For a central cocharacter, the reverse compact-picture integral does not depend on the
parameter. -/
theorem conditionalReverseCompactFamily_eq_of_levi_eq_top (hlevi : levi χ = ⊤)
    (z w : reverseFullDomainRegion χ K hK A) :
    conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z =
      conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A w := by
  refine LinearMap.ext fun φ => compactPictureValues_injective (decomposition χ) K A ?_
  rw [conditionalReverseCompactFamily_values_of_levi_eq_top χ hRefl hCST hG K hK hPK hOppK A
      hlevi z φ,
    conditionalReverseCompactFamily_values_of_levi_eq_top χ hRefl hCST hG K hK hPK hOppK A
      hlevi w φ]

/-- **Forward continuation data of a central cocharacter.** The denominator is the constant `1`
and the numerator is the constant operator, the forward compact-picture integral at the trivial
parameter. -/
def forwardContinuationOfLeviEqTop (hlevi : levi χ = ⊤) :
    ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A where
  denominator := 1
  denominator_nonzero _ := by simp
  numerator _ := conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A
    ⟨1, mem_forwardFullDomainRegion_of_levi_eq_top χ K hK A hlevi 1⟩
  polynomial := isPolynomialOperatorOn_const _
  clears z := by
    rw [Subalgebra.coe_one, Pi.one_apply, one_smul]
    exact conditionalForwardCompactFamily_eq_of_levi_eq_top χ K hK A hRefl hCST hG hPK hOppK
      hlevi _ _

/-- **Reverse continuation data of a central cocharacter.** The denominator is the constant `1`
and the numerator is the constant operator, the reverse compact-picture integral at the trivial
parameter. -/
def reverseContinuationOfLeviEqTop (hlevi : levi χ = ⊤) :
    ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A where
  denominator := 1
  denominator_nonzero _ := by simp
  numerator _ := conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A
    ⟨1, mem_reverseFullDomainRegion_of_levi_eq_top χ K hK A hlevi 1⟩
  polynomial := isPolynomialOperatorOn_const _
  clears z := by
    rw [Subalgebra.coe_one, Pi.one_apply, one_smul]
    exact conditionalReverseCompactFamily_eq_of_levi_eq_top χ K hK A hRefl hCST hG hPK hOppK
      hlevi _ _

/-! #### Irreducibility of the induced representations -/

include hG in
/-- **Induction from the whole group keeps irreducibility.** If the centralizer of `χ` is all
of `G(F)` and `A` is irreducible, then the Levi-normalized induction of every unramified twist
of `A` is irreducible: through the trivial radical it is the twist of `A`, pulled back to
`G(F)`. -/
theorem unramifiedLeviInduction_isIrreducible_of_levi_eq_top (hlevi : levi χ = ⊤)
    (hA : A.IsIrreducible) (z : unramifiedCharacters (normCharacters χ)) :
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible := by
  set B := A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))
  have hB : B.IsIrreducible := (SmoothRep.isIrreducible_twist_iff _ _ A).mpr hA
  have hpull : (HarishChandraSchwartz.fullLeviAmbientSmoothRep (levi χ) hlevi B).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff B.representation
      (HarishChandraSchwartz.fullLeviGroupEquiv (levi χ) hlevi)).mpr hB
  exact LengthTwo.isIrreducible_of_equiv
    ((HarishChandraSchwartz.fullLeviInductionEquiv (decomposition χ) (radical_isClosed χ)
      ((decomposition χ).parabolic_eq_top_of_levi_eq_top hlevi) hlevi
      (radical_eq_bot_of_levi_eq_top χ hlevi) B).symm.trans
      (normalizedInductionLeviEquiv (decomposition χ) (radical_isClosed χ)
        (radical_unimodular χ hG) B)) hpull

end DynamicFullLevi

end Langlands.Plancherel
