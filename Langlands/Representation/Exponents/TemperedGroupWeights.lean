import Langlands.Representation.Exponents.NormalizedTemperedFullGroupProof
import Langlands.Representation.Exponents.CentralCharacterIdentityJacquet
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.GroupScheme.Rational.IdentityParabolic

/-! # Generalized split-component weights of tempered representations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedWeightAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
  (ha : IsSplitComponent a)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The actual identity Jacquet quotient as an intertwiner for the split component. -/
def identityJacquetCentralQuotient
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Representation.IntertwiningMap (π.representation.comp (rationalPoints.map a))
      ((((jacquetFunctor (𝟙 G) (𝟙 G) (kernelUnit G)
        hG.isParabolicSubgroup_id hG.isGeometricUnipotentRadical_kernelUnit
        hG.isRationalLeviSubgroup_id isIso_subgroupMultiplication_id_kernelUnit).obj π).representation).comp
          (splitComponentPointsMap ((𝟙 G) ≫ (𝟙 G)) a)) :=
  normalizedJacquetCentralQuotient
    (pointImage (kernelUnit G ≫ 𝟙 G)) (pointImage ((𝟙 G) ≫ (𝟙 G)))
    (isClosed_pointImage_comp (𝟙 G) (kernelUnit G)
      hG.isParabolicSubgroup_id.isClosedSubgroup
      hG.isGeometricUnipotentRadical_kernelUnit.1.isClosedSubgroup)
    (pointImage_le_normalizer (𝟙 G) (𝟙 G) (kernelUnit G)
      hG.isGeometricUnipotentRadical_kernelUnit)
    π (rationalPoints.map a) (splitComponentPointsMap ((𝟙 G) ≫ (𝟙 G)) a)
    (fun _ => rfl) ha.isCentralSplitTorus.isCentral.map_mem_center

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The identity Jacquet quotient is injective because its actual radical is trivial. -/
theorem identityJacquetCentralQuotient_injective
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Function.Injective (identityJacquetCentralQuotient hG ha π) := by
  intro x y hxy
  have hbot := pointImage_identity_radical_eq_bot hG (kernelUnit G)
    hG.isGeometricUnipotentRadical_kernelUnit
  have he := congrArg (endpointCoinvariantsEquiv _ hbot π) hxy
  change endpointCoinvariantsEquiv _ hbot π (Jacquet.Localization.mk _ _ 1 x) =
    endpointCoinvariantsEquiv _ hbot π (Jacquet.Localization.mk _ _ 1 y) at he
  simpa only [endpointCoinvariantsEquiv_mk] using he

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The identity normalized Jacquet quotient preserves every generalized
split-component eigencharacter, without a scalar central-character premise. -/
theorem isNormalizedJacquetExponent_identity_of_isGeneralizedEigencharacter
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter (π.representation.comp (rationalPoints.map a)) χ) :
    IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) (kernelUnit G)
      hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id
      hG.isGeometricUnipotentRadical_kernelUnit isIso_subgroupMultiplication_id_kernelUnit
      ha π χ := by
  let f := identityJacquetCentralQuotient hG ha π
  obtain ⟨d, x, hx, hd⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  have hfx : f x ≠ 0 := by
    intro hz
    apply hx
    exact identityJacquetCentralQuotient_injective hG ha π
      (hz.trans f.toLinearMap.map_zero.symm)
  apply (isNormalizedJacquetExponent_iff (𝟙 G) (𝟙 G) (kernelUnit G)
    hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id
    hG.isGeometricUnipotentRadical_kernelUnit isIso_subgroupMultiplication_id_kernelUnit
    ha π χ).mpr
  apply (isGeneralizedEigencharacter_iff _ _).mpr
  refine ⟨d, f x, hfx, ?_⟩
  have hmem : x ∈ characterSpace (π.representation.comp (rationalPoints.map a)) χ d :=
    (mem_characterSpace _ _ _ _).mpr hd
  have hm := map_mem_characterSpace_of_intertwining f.toLinearMap
    (fun t => (f.isIntertwining' t).symm) χ d hmem
  exact (mem_characterSpace _ _ _ _).mp hm

/-- Every generalized split-component eigencharacter of a tempered representation
has zero normalized real part and is pointwise unitary. -/
theorem tempered_generalizedEigencharacter_unitary
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : IsNormalizedExponentTempered hG π)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter (π.representation.comp (rationalPoints.map a)) χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 ∧
      ∀ x : rationalPoints A.toGrp, ‖(χ x : ℂ)‖ = 1 := by
  exact normalizedTemperedFullGroupExponent k G hG π A a
    hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id ha
    _ (kernelUnit G) hG.isGeometricUnipotentRadical_kernelUnit
    isIso_subgroupMultiplication_id_kernelUnit χ hπ
    (isNormalizedJacquetExponent_identity_of_isGeneralizedEigencharacter hG ha π χ hχ)

/-- A nonunitary generalized split-component weight space in a tempered
representation is zero. -/
theorem tempered_generalizedWeightSpace_eq_bot
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : IsNormalizedExponentTempered hG π)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0) :
    generalizedWeightSpace π.representation (rationalPoints.map a) χ
      ha.isCentralSplitTorus.isCentral.map_mem_center = ⊥ := by
  by_contra hne
  exact hχ (tempered_generalizedEigencharacter_unitary hG ha π hπ χ
    ((generalizedWeightSpace_ne_bot_iff _ χ _ π.isSmooth).mp hne)).1

end Langlands.Aubert.General.RepresentedParabolic
