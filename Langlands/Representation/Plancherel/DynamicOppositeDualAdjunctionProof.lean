import Langlands.Representation.Plancherel.OppositeIntertwiningDualAdjunction
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof

/-! # Proof of the duality adjunction of the opposite standard integrals

This module proves `ConditionalDynamicOppositeDualAdjunctionStatement`, Waldspurger 2003,
IV.1 (11), for the Library's actual opposite standard integrals `conditionalForwardCompactFamily`
and `conditionalReverseCompactFamily` and the contragredient pairing
`compactPictureDualPairing`. Both identities specialize
`OppositeIntertwiningDualAdjunction.compactPicture_dualAdjunction`: the first to `P = P_G(χ)`,
`P' = P̄ = P_G(χ⁻¹)` and the second with the roles of `P` and `P̄` exchanged, in both cases with
`M = Z_G(χ)`, the source Haar measures of the Library's families, and the Haar measure on `M(F)`
giving `M(F) ∩ K` mass one. That measure is right invariant because `M(F)` is unimodular
(`DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeDualAdjunctionProof

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily Haar
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open OppositeIntertwiningHermitianAdjunction OppositeIntertwiningDualAdjunction
open DynamicOppositeHermitianAdjunctionProof

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
  Langlands.Plancherel.contragredientScalarPointMeasurable
  Langlands.Plancherel.contragredientScalarPointBorel
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
  DynamicOppositeHermitianAdjunctionProof.hermitianProofLeviMeasurable
  DynamicOppositeHermitianAdjunctionProof.hermitianProofLeviBorel
  DynamicOppositeHermitianAdjunctionProof.hermitianProofLeviLocallyCompact
  DynamicOppositeHermitianAdjunctionProof.hermitianProofRadicalLocallyCompact
  DynamicOppositeHermitianAdjunctionProof.hermitianProofLeviSecondCountable
  DynamicOppositeHermitianAdjunctionProof.hermitianProofRadicalSecondCountable
  DynamicOppositeHermitianAdjunctionProof.hermitianProofOppositeRadicalSecondCountable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

omit [LocallyOfFiniteType G.X.hom] in
/-- The inverse parameter pairs with the original one to `1`: for every `m ∈ M(F)`,
`z(m) · z⁻¹(m) = 1` after transport to the literal Levi. -/
theorem parameterTransport_mul_inv (z : unramifiedCharacters (normCharacters χ))
    (m : levi χ) :
    ((parameterTransport χ z).val m : ℂ) * ((parameterTransport χ z⁻¹).val m : ℂ) = 1 := by
  rw [map_inv, unramifiedCharacters_inv_val_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel,
    map_one, Units.val_one]

/-- The first identity of the duality adjunction for fixed data: `J_{P̄|P}(A ⊗ z)` and
`J_{P|P̄}(Ǎ ⊗ z⁻¹)` are adjoint for the contragredient pairing. -/
theorem forwardDualAdjunction
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
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : forwardFullDomainRegion χ K hK A)
    (hz : z.val⁻¹ ∈ reverseFullDomainRegion χ K hK A.contragredient)
    (φ : CompactInductionPicture (decomposition χ) K A)
    (φ' : CompactInductionPicture (oppositeDecomposition χ) K A.contragredient) :
    compactPictureDualPairing (oppositeDecomposition χ) K hK A
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) φ' =
      compactPictureDualPairing (decomposition χ) K hK A φ
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A.contragredient
          ⟨z.val⁻¹, hz⟩ φ') := by
  have hMr : (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)).IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one (levi_modularCharacter_eq_one χ hG) _
  exact compactPicture_dualAdjunction (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) (oppositeParabolic_isClosed χ) hOppK
    (oppositeProjection_continuous χ) (radical_inf_oppositeRadical χ) hKsplit hOppKsplit
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
    (parameterTransport χ z.val) (parameterTransport χ z.val⁻¹)
    (parameterTransport_mul_inv χ z.val)
    (conditionalForwardFamily χ K hK hRefl hCST hG A z)
    (conditionalReverseFamily χ K hK hRefl hCST hG A.contragredient ⟨z.val⁻¹, hz⟩)
    (conditionalForwardFamily_spec χ K hK hRefl hCST hG A z)
    (conditionalReverseFamily_spec χ K hK hRefl hCST hG A.contragredient ⟨z.val⁻¹, hz⟩) φ φ'

/-- The second identity of the duality adjunction for fixed data: `J_{P|P̄}(A ⊗ z)` and
`J_{P̄|P}(Ǎ ⊗ z⁻¹)` are adjoint for the contragredient pairing. -/
theorem reverseDualAdjunction
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
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : reverseFullDomainRegion χ K hK A)
    (hz : z.val⁻¹ ∈ forwardFullDomainRegion χ K hK A.contragredient)
    (ψ : CompactInductionPicture (oppositeDecomposition χ) K A)
    (ψ' : CompactInductionPicture (decomposition χ) K A.contragredient) :
    compactPictureDualPairing (decomposition χ) K hK A
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z ψ) ψ' =
      compactPictureDualPairing (oppositeDecomposition χ) K hK A ψ
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A.contragredient
          ⟨z.val⁻¹, hz⟩ ψ') := by
  have hMr : (subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)).IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one (levi_modularCharacter_eq_one χ hG) _
  exact compactPicture_dualAdjunction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K (oppositeParabolic_isClosed χ) hK hOppK
    (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (oppositeProjection_continuous χ) (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) (parabolic_isClosed χ) hPK (projection_continuous χ)
    ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)) hOppKsplit hKsplit
    (fun m =>
      RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
        hRefl hCST hG χ (oppositeRadical χ) (levi χ) (radical χ) rfl rfl rfl
        (oppositeRadical_isClosed χ) (radical_isClosed χ)
        (oppositeDecomposition χ).levi_le_normalizer (decomposition χ).levi_le_normalizer m)
    (μM := subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ))
    (subgroupCompactOpenHaar_mass K hK _ _)
    (μU := oppositeRadicalHaar χ K hK) (subgroupCompactOpenHaar_mass K hK _ _)
    (μU' := radicalHaar χ K hK) (subgroupCompactOpenHaar_mass K hK _ _)
    (μI := reverseIntersectionHaar χ K hK)
    (sourceIntersectionHaar_univ K hK _ _ _ _
      ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)))
    (μI' := forwardIntersectionHaar χ K hK)
    (sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ))
    (reverseQuotientMeasure_isCompatible χ K hK) (forwardQuotientMeasure_isCompatible χ K hK)
    (parameterTransport χ z.val) (parameterTransport χ z.val⁻¹)
    (parameterTransport_mul_inv χ z.val)
    (conditionalReverseFamily χ K hK hRefl hCST hG A z)
    (conditionalForwardFamily χ K hK hRefl hCST hG A.contragredient ⟨z.val⁻¹, hz⟩)
    (conditionalReverseFamily_spec χ K hK hRefl hCST hG A z)
    (conditionalForwardFamily_spec χ K hK hRefl hCST hG A.contragredient ⟨z.val⁻¹, hz⟩) ψ ψ'

end Langlands.Plancherel.DynamicOppositeDualAdjunctionProof

namespace Langlands.Plancherel

/-- **Duality adjunction of the opposite standard integrals** (Waldspurger 2003, IV.1 (11)). -/
theorem conditionalDynamicOppositeDualAdjunction :
    ConditionalDynamicOppositeDualAdjunctionStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A
  exact ⟨fun z hz φ φ' => DynamicOppositeDualAdjunctionProof.forwardDualAdjunction χ hRefl hCST
      hG K hK hPK hOppK hKsplit hOppKsplit A z hz φ φ',
    fun z hz ψ ψ' => DynamicOppositeDualAdjunctionProof.reverseDualAdjunction χ hRefl hCST hG K
      hK hPK hOppK hKsplit hOppKsplit A z hz ψ ψ'⟩

end Langlands.Plancherel
