import Langlands.Representation.Plancherel.OppositeIntertwiningHermitianAdjunction
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Proof of the Hermitian adjunction of the opposite standard integrals

This module proves `ConditionalDynamicOppositeHermitianAdjunctionStatement`, the Hermitian
form of Waldspurger 2003, IV.1 (11), for the Library's actual opposite standard integrals
`conditionalForwardCompactFamily` and `conditionalReverseCompactFamily`. It specializes
`OppositeIntertwiningHermitianAdjunction.compactPicture_adjunction` to `P = P_G(χ)`,
`P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`, with the source Haar measures of the Library's families and
the Haar measure on `M(F)` giving `M(F) ∩ K` mass one. That measure is right invariant
because `M(F)` is unimodular (`RationalPointFamily.rationalReductiveUnimodularity` for the
connected reductive centralizer scheme, transported to the literal Levi).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeHermitianAdjunctionProof

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily Haar
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
local instance hermitianProofLeviMeasurable : MeasurableSpace (levi χ) := borel _

local instance hermitianProofLeviBorel : BorelSpace (levi χ) := ⟨rfl⟩

local instance hermitianProofLeviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

local instance hermitianProofRadicalLocallyCompact : LocallyCompactSpace (radical χ) :=
  (radical_isClosed χ).locallyCompactSpace

local instance hermitianProofLeviSecondCountable : SecondCountableTopology (levi χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (levi χ : Set (RationalPoint F G.X))

local instance hermitianProofRadicalSecondCountable : SecondCountableTopology (radical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology (radical χ : Set (RationalPoint F G.X))

local instance hermitianProofOppositeRadicalSecondCountable :
    SecondCountableTopology (oppositeRadical χ) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (oppositeRadical χ : Set (RationalPoint F G.X))

/-- The literal Levi `M(F) = Z_G(χ)(F)` is unimodular: its actual closed representative is
the group of rational points of the connected reductive centralizer scheme. -/
theorem levi_modularCharacter_eq_one (hG : IsConnectedReductive G) (m : levi χ) :
    modularCharacter m = 1 := by
  have hM := parameterScheme_isConnectedReductive χ hG
  let e := parameterHomeomorph χ
  have ht2 : T2Space (RationalPoint F (parameterScheme χ).X) :=
    e.toHomeomorph.isEmbedding.t2Space
  have hlc : LocallyCompactSpace (RationalPoint F (parameterScheme χ).X) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have h1 := @RationalPointFamily.rationalReductiveUnimodularity.{u} F _ _ _ _
    (parameterScheme χ) hM hlc
    (inferInstanceAs (NonarchimedeanGroup (RationalPoint F (parameterScheme χ).X))) ht2
    standardCocharacter (e.symm m)
  simpa only [e.apply_symm_apply] using
    (modularCharacter_continuousMulEquiv e (e.symm m)).trans h1

omit [LocallyOfFiniteType G.X.hom] in
/-- The conjugate-inverse parameter pairs with the original one to `1`: for every
`m ∈ M(F)`, `conj(z(m)) · z†(m) = 1` after transport to the literal Levi. -/
theorem conj_parameterTransport_mul_conjInv
    (z : unramifiedCharacters (normCharacters χ)) (m : levi χ) :
    starRingEnd ℂ ((parameterTransport χ z).val m : ℂ) *
      ((parameterTransport χ (unramifiedConjInv (normCharacters χ) z)).val m : ℂ) = 1 := by
  rw [parameterTransport, unramifiedCharactersHomeomorph_apply,
    unramifiedCharactersHomeomorph_apply, unramifiedConjInv_val, characterConjInv_apply_coe]
  exact mul_inv_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr (Units.ne_zero _))

/-- The Hermitian adjunction for fixed data; see
`conditionalDynamicOppositeHermitianAdjunction`. -/
theorem hermitianAdjunction
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (b : InvariantPositiveForm A.representation)
    (z : forwardFullDomainRegion χ K hK A)
    (hz : unramifiedConjInv (normCharacters χ) z.val ∈ reverseFullDomainRegion χ K hK A)
    (φ : CompactInductionPicture (decomposition χ) K A)
    (φ' : CompactInductionPicture (oppositeDecomposition χ) K A) :
    compactPictureHermitianPairing (oppositeDecomposition χ) K hK A b
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) φ' =
      compactPictureHermitianPairing (decomposition χ) K hK A b φ
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A
          ⟨unramifiedConjInv (normCharacters χ) z.val, hz⟩ φ') := by
  have hMr : (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)).IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one (levi_modularCharacter_eq_one χ hG) _
  exact compactPicture_adjunction (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) (oppositeParabolic_isClosed χ) hOppK
    (oppositeProjection_continuous χ) b (radical_inf_oppositeRadical χ) hKsplit hOppKsplit
    (fun m => (mul_comm _ _).trans
      (RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
        hRefl hCST hG χ (oppositeRadical χ) (levi χ) (radical χ) rfl rfl rfl
        (oppositeRadical_isClosed χ) (radical_isClosed χ)
        (oppositeDecomposition χ).levi_le_normalizer (decomposition χ).levi_le_normalizer m))
    (μM := subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ))
    (subgroupCompactOpenHaar_mass K hK _ _)
    (μU := radicalHaar χ K hK) (subgroupCompactOpenHaar_mass K hK _ _)
    (μU' := oppositeRadicalHaar χ K hK) (subgroupCompactOpenHaar_mass K hK _ _)
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

end Langlands.Plancherel.DynamicOppositeHermitianAdjunctionProof

namespace Langlands.Plancherel

/-- **Hermitian adjunction of the opposite standard integrals** (Waldspurger 2003,
IV.1 (11), Hermitian form used in IV.3 (6)). -/
theorem conditionalDynamicOppositeHermitianAdjunction :
    ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A b z hz φ φ'
  exact DynamicOppositeHermitianAdjunctionProof.hermitianAdjunction χ hRefl hCST hG K hK hPK
    hOppK hKsplit hOppKsplit A b z hz φ φ'

end Langlands.Plancherel
