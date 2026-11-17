import Langlands.Representation.Plancherel.OppositeIntertwiningConjugateDomain
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof
import Langlands.Representation.Aubert.General.AlternatingOperator

/-! # Conjugate-inverse domains for the actual dynamic opposite integrals -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeConjugateDomain

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily Haar
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open OppositeIntertwiningHermitianAdjunction DynamicOppositeHermitianAdjunctionProof

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

/-- The Borel structure on the literal Levi. -/
local instance conjugateDomainLeviMeasurable : MeasurableSpace (levi χ) := borel _

local instance conjugateDomainLeviBorel : BorelSpace (levi χ) := ⟨rfl⟩

local instance conjugateDomainLeviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

local instance conjugateDomainRadicalLocallyCompact : LocallyCompactSpace (radical χ) :=
  (radical_isClosed χ).locallyCompactSpace

local instance conjugateDomainLeviSecondCountable : SecondCountableTopology (levi χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (levi χ : Set (RationalPoint F G.X))

local instance conjugateDomainRadicalSecondCountable : SecondCountableTopology (radical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (radical χ : Set (RationalPoint F G.X))

local instance conjugateDomainOppositeRadicalSecondCountable :
    SecondCountableTopology (oppositeRadical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (oppositeRadical χ : Set (RationalPoint F G.X))

/-- The exact positive comparison factor for the original source Haar
normalizations of the actual two opposite integrals. -/
def adjunctionScale
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X))) : ℝ :=
  hermitianAdjunctionScale K
    (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ))
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)

/-- The comparison factor is strictly positive, for the actual unchanged K. -/
theorem adjunctionScale_pos
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X))) :
    0 < adjunctionScale χ K hK :=
  LeviInvariantIwasawaExchange.iwasawaExchangeRatio_toReal_pos
    (decomposition χ) (oppositeDecomposition χ) K
    (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ))
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hK
    (projection_continuous χ) (oppositeProjection_continuous χ)

/-- The actual forward full convergence domain is carried into the reverse
full domain by conjugate inversion, for every admissible unitary coefficient
representation. No compact-splitting premise is used. -/
theorem mem_reverseFullDomainRegion_of_forward
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (hA : A.IsAdmissible)
    (b : InvariantPositiveForm A.representation)
    (z : unramifiedCharacters (normCharacters χ))
    (hz : z ∈ forwardFullDomainRegion χ K hK A) :
    unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A := by
  have hMr : (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)).IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one (levi_modularCharacter_eq_one χ hG) _
  exact domain_eq_top_of_forward (decomposition χ) (radical_isClosed χ)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ) b
    (χ₁ := (parameterTransport χ z).val.toMonoidHom)
    (χ₂ := (parameterTransport χ (unramifiedConjInv (normCharacters χ) z)).val.toMonoidHom)
    (hχ₁ := unramifiedCharacter_isOpen_ker _ _) (hχ₂ := unramifiedCharacter_isOpen_ker _ _)
    (radical_inf_oppositeRadical χ) K hK hPK hOppK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ)
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (fun m => (mul_comm _ _).trans
      (RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
        hRefl hCST hG χ (oppositeRadical χ) (levi χ) (radical χ) rfl rfl rfl
        (oppositeRadical_isClosed χ) (radical_isClosed χ)
        (oppositeDecomposition χ).levi_le_normalizer (decomposition χ).levi_le_normalizer m))
    (conj_parameterTransport_mul_conjInv χ z)
    (compactOpenCofinal_of_nonarchimedean (levi χ)) hA
    (μM := subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ))
    (μU := radicalHaar χ K hK) (μU' := oppositeRadicalHaar χ K hK)
    (μI := forwardIntersectionHaar χ K hK)
    (sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ))
    (μI' := reverseIntersectionHaar χ K hK)
    (sourceIntersectionHaar_univ K hK _ _ _ _
      ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)))
    (forwardQuotientMeasure_isCompatible χ K hK) (reverseQuotientMeasure_isCompatible χ K hK)
    («μ» := RankinSelberg.normalizedCompactOpenHaar K hK)
    (levi_isClosed χ) (conditionalReverseSquaredModulus χ hRefl hCST hG) hz

end Langlands.Plancherel.DynamicOppositeConjugateDomain
