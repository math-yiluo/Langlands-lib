import Langlands.Representation.Plancherel.DynamicOppositeSquareIntegrablePositivity
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryInverseRegularity
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement

/-! # Exact square-integrable scalar target reduced to inverse regularity -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General UnramifiedOperatorFamily
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

/-- The remaining inverse-regularity obligation with exactly the original
square-integrable scalar target's hypotheses and independent universes. -/
def ConditionalDynamicOppositeSquareIntegrableInverseRegularStatement : Prop :=
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
      ∀ z : unramifiedCharacters (normCharacters χ),
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionRegularAt (parameterScheme χ) (parameterProjection_continuous χ)
          (parameterScheme_isConnectedReductive χ hG)
          (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
            p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z


/-- The exact scalar target follows once inverse regularity at all unitary
parameters is proved with the same original hypotheses. -/
theorem conditionalDynamicOppositeUnitaryScalar_of_squareIntegrable_regular
    (R : ConditionalDynamicOppositeSquareIntegrableInverseRegularStatement.{u, uV}) :
    ConditionalDynamicOppositeUnitaryScalarStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK A p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi C _ hC _ _ μM _ _ hsq
  have hP := DynamicOppositeSquareIntegrablePositivity.unitaryPositive_of_squareIntegrable
    χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
  have hR := R χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
  have hpd : p.denominator ≠ 0 := fun h0 => hneForward.elim fun w hw =>
    p.denominator_nonzero ⟨w, hDForwardΩ hw⟩ (by rw [h0]; rfl)
  have hqd : q.denominator ≠ 0 := fun h0 => hneReverse.elim fun w hw =>
    q.denominator_nonzero ⟨w, hDReverseΩ hw⟩ (by rw [h0]; rfl)
  let := rationalUnramifiedRegularFunctions_isDomain (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
  refine ⟨hP.1, fun z hz => ?_⟩
  exact RationalFunctionRegularAt.nonnegAt_of_unitary (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) (hR z hz) hz
    (p.denominator * q.denominator) (mul_ne_zero hpd hqd)
    (fun w hw hgw =>
      have hgw' : p.denominator.val w * q.denominator.val w ≠ 0 := hgw
      ((hP.2 w ⟨left_ne_zero_of_mul hgw', right_ne_zero_of_mul hgw'⟩ hw).2).nonnegAt)

end Langlands.Plancherel
