import Langlands.Representation.Plancherel.CompactOppositeScaledAdjunction
import Langlands.Representation.Plancherel.DynamicOppositeConjugateDomain
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryNonnegativity

/-! # Exact adjunction using positive rescaling for the actual compact pictures -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeScaledAdjunction

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
local instance scaledAdjunctionLeviMeasurable : MeasurableSpace (levi χ) := borel _

local instance scaledAdjunctionLeviBorel : BorelSpace (levi χ) := ⟨rfl⟩

local instance scaledAdjunctionLeviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

local instance scaledAdjunctionRadicalLocallyCompact : LocallyCompactSpace (radical χ) :=
  (radical_isClosed χ).locallyCompactSpace

local instance scaledAdjunctionLeviSecondCountable : SecondCountableTopology (levi χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (levi χ : Set (RationalPoint F G.X))

local instance scaledAdjunctionRadicalSecondCountable : SecondCountableTopology (radical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (radical χ : Set (RationalPoint F G.X))

local instance scaledAdjunctionOppositeRadicalSecondCountable :
    SecondCountableTopology (oppositeRadical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (oppositeRadical χ : Set (RationalPoint F G.X))

/-- The source compact form rescaled by the strictly positive actual source
normalization ratio. -/
def scaledSourceSesq
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (b : InvariantPositiveForm A.representation) :
    CompactInductionPicture (decomposition χ) K A →ₗ⋆[ℂ]
      CompactInductionPicture (decomposition χ) K A →ₗ[ℂ] ℂ :=
  scaledSesq (DynamicOppositeConjugateDomain.adjunctionScale χ K hK)
    (compactPictureSesq (decomposition χ) K hK A b)

/-- The rescaled source form has nonnegative real diagonal values. -/
theorem scaledSourceSesq_self
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (b : InvariantPositiveForm A.representation)
    (φ : CompactInductionPicture (decomposition χ) K A) :
    ∃ r : ℝ, 0 ≤ r ∧ scaledSourceSesq χ K hK A b φ φ = (r : ℂ) :=
  scaledSesq_self _ (DynamicOppositeConjugateDomain.adjunctionScale_pos χ K hK).le _
    (compactPictureHermitianPairing_self (decomposition χ) K hK A b) φ

/-- The rescaled source form remains definite. -/
theorem scaledSourceSesq_self_ne_zero
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (b : InvariantPositiveForm A.representation)
    {φ : CompactInductionPicture (decomposition χ) K A} (hφ : φ ≠ 0) :
    scaledSourceSesq χ K hK A b φ φ ≠ 0 :=
  scaledSesq_self_ne_zero _ (DynamicOppositeConjugateDomain.adjunctionScale_pos χ K hK) _ φ
    (compactPictureHermitianPairing_self_ne_zero (decomposition χ) K hK A b hφ)

/-- Exact adjunction for the actual opposite compact integrals using the
positive rescaled source form, without compact splitting. -/
theorem hermitianAdjunction_scaled
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (b : InvariantPositiveForm A.representation)
    (z : forwardFullDomainRegion χ K hK A)
    (hz : unramifiedConjInv (normCharacters χ) z.val ∈ reverseFullDomainRegion χ K hK A)
    (φ : CompactInductionPicture (decomposition χ) K A)
    (φ' : CompactInductionPicture (oppositeDecomposition χ) K A) :
    compactPictureHermitianPairing (oppositeDecomposition χ) K hK A b
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) φ' =
      scaledSourceSesq χ K hK A b φ
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A
          ⟨unramifiedConjInv (normCharacters χ) z.val, hz⟩ φ') := by
  have hMr : (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)).IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one (levi_modularCharacter_eq_one χ hG) _
  have he := compactPicture_adjunction_scaled (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) (oppositeParabolic_isClosed χ) hOppK
    (oppositeProjection_continuous χ) b (radical_inf_oppositeRadical χ)
    (fun m => (mul_comm _ _).trans
      (RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
        hRefl hCST hG χ (oppositeRadical χ) (levi χ) (radical χ) rfl rfl rfl
        (oppositeRadical_isClosed χ) (radical_isClosed χ)
        (oppositeDecomposition χ).levi_le_normalizer (decomposition χ).levi_le_normalizer m))
    (μM := subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ))
    (μU := radicalHaar χ K hK)
    (μU' := oppositeRadicalHaar χ K hK)
    (μI := forwardIntersectionHaar χ K hK)
    (sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ))
    (μI' := reverseIntersectionHaar χ K hK)
    (sourceIntersectionHaar_univ K hK _ _ _ _
      ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)))
    (forwardQuotientMeasure_isCompatible χ K hK) (reverseQuotientMeasure_isCompatible χ K hK)
    (parameterTransport χ z.val)
    (parameterTransport χ (unramifiedConjInv (normCharacters χ) z.val))
    (conj_parameterTransport_mul_conjInv χ z.val)
    (conditionalForwardFamily χ K hK hRefl hCST hG A z)
    (conditionalReverseFamily χ K hK hRefl hCST hG A
      ⟨unramifiedConjInv (normCharacters χ) z.val, hz⟩)
    (conditionalForwardFamily_spec χ K hK hRefl hCST hG A z)
    (conditionalReverseFamily_spec χ K hK hRefl hCST hG A
      ⟨unramifiedConjInv (normCharacters χ) z.val, hz⟩) φ φ'

  simpa only [scaledSourceSesq, scaledSesq_apply, compactPictureSesq_apply,
    DynamicOppositeConjugateDomain.adjunctionScale, Complex.real_smul,
    conditionalForwardCompactFamily, conditionalReverseCompactFamily] using he

end Langlands.Plancherel.DynamicOppositeScaledAdjunction
