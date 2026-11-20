import Langlands.Representation.Plancherel.DynamicOppositeSquareIntegrableRegularityReduction
import Langlands.Representation.Plancherel.DynamicOppositeInverseBound
import Langlands.Representation.Plancherel.RationalRankOneProductDifferences

/-! # The exact opposite scalar from the actual pointwise rank-one product -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General UnramifiedOperatorFamily ValuationKernelCoordinates
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

/-- The actual pointwise product obligation under the exact original
square-integrable scalar hypotheses. Its constant retains the original
Haar normalization. -/
def ConditionalDynamicOppositeSquareIntegrableRankOneProductStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (_hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
    [Finite (levi χ ⧸ (commonNormKernel (leviNormCharacters χ) ⊔ C))]
    (_hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM),
    ∃ charts : List (RankOneTranslationChart (parameterScheme χ)),
      HasDenseRankOneProduct (parameterScheme χ)
        (parameterScheme_isConnectedReductive χ hG) charts
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)

set_option maxHeartbeats 1600000 in
/-- The actual pointwise product and the already proved analytic estimates
imply the exact full-unitary opposite-scalar target. -/
theorem conditionalDynamicOppositeUnitaryScalar_of_denseRankOneProduct
    (hproduct : ConditionalDynamicOppositeSquareIntegrableRankOneProductStatement.{u, uV}) :
    ConditionalDynamicOppositeUnitaryScalarStatement.{u, uV} := by
  apply conditionalDynamicOppositeUnitaryScalar_of_squareIntegrable_regular
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK A p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi C _ hC _ _ μM _ _ hsq z hz
  let jP := conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
    p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi
  have hP := DynamicOppositeSquareIntegrablePositivity.unitaryPositive_of_squareIntegrable
    χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
  have hj : jP ≠ 0 := hP.1
  obtain ⟨charts, hpProd⟩ := hproduct χ hRefl hCST hG K hK hPK hOppK A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
  obtain ⟨B, hB, hbound⟩ :=
    DynamicOppositeInverseBound.unitaryCommonRegularInverseBounded_of_squareIntegrable
      χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
      hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
  have hpd := p.denominator_ne_zero (hneForward.mono hDForwardΩ)
  have hqd := q.denominator_ne_zero (hneReverse.mono hDReverseΩ)
  let : IsDomain (unramifiedRegularFunctions (normCharacters χ)) :=
    rationalUnramifiedRegularFunctions_isDomain (parameterScheme χ) (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
  have hDunit : Dense {w : unitaryUnramifiedCharacters (normCharacters χ) |
      unitaryToUnramified (parameterScheme χ) w ∈ p.regularRegion ∩ q.regularRegion} :=
    (ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG)
      (p.denominator * q.denominator) (mul_ne_zero hpd hqd)).mono (fun w hw =>
        have hw' : p.denominator.val (unitaryToUnramified (parameterScheme χ) w) *
            q.denominator.val (unitaryToUnramified (parameterScheme χ) w) ≠ 0 := hw
        ⟨left_ne_zero_of_mul hw', right_ne_zero_of_mul hw'⟩)
  have hb : HasDenseUnitaryNormBound (parameterScheme_isConnectedReductive χ hG) jP⁻¹ :=
    ⟨_, hDunit, B, hB.le, fun w hw => hbound (unitaryToUnramified (parameterScheme χ) w) hw w.property⟩
  have hprodInv : HasDenseRankOneProduct (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG) charts jP⁻¹ :=
    HasDenseRankOneProduct.inv (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG) hpProd
  have hreg : RationalFunctionUnitaryRegular (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG) jP⁻¹ :=
    unitaryRegular_of_denseRankOneProduct (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG) charts jP⁻¹ (inv_ne_zero hj) hprodInv hb
  let w : unitaryUnramifiedCharacters (normCharacters χ) := ⟨z.val, hz⟩
  unfold RationalFunctionUnitaryRegular at hreg
  exact hreg w

end Langlands.Plancherel
