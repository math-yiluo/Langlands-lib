import Langlands.Representation.Plancherel.RationalRankOneAmbientRegularity
import Langlands.Representation.Plancherel.DynamicOppositeAmbientTwist
import Langlands.Representation.Plancherel.DynamicOppositeInverseBound
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericLocus
import Langlands.GroupScheme.Rational.RationalCocharacterParabolicModels
import Langlands.Global.AdelicRestrictionSplitCentreCanonical

/-! # Regularity of the inverse opposite scalar for a maximal proper Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel.DynamicOppositeMaximalLeviRegularity

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)

set_option hygiene false in
local notation "Mχ" => parameterScheme χ

set_option hygiene false in
local notation "iχ" => Dynamic.Affine.centralizerHom χ

set_option hygiene false in
local notation "Xχ" => unramifiedCharacters (normCharacters χ)

set_option hygiene false in
local notation "Uχ" => unitaryUnramifiedCharacters (normCharacters χ)

set_option hygiene false in
local notation "hMχ" => parameterScheme_isConnectedReductive χ hG

set_option hygiene false in
local notation "hπχ" => parameterProjection_continuous χ

/-- The actual dynamic parabolic is proper and maximal among proper rational
parabolics, expressed through its fixed-embedded-Levi model. -/
def IsMaximalProper : Prop :=
  let d := fixedLeviParabolicModel hG χ (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
  ¬ IsIso d.p ∧
  ∀ (Q : GroupScheme (Spec (CommRingCat.of F))) (q : Q ⟶ G) (j : d.P ⟶ Q),
    IsParabolicSubgroup q → j ≫ q = d.p → IsIso j ∨ IsIso q

set_option maxHeartbeats 800000 in
/-- Choose a split component of the actual common Levi and then choose
product coordinates adapted to its original inclusion into the ambient group. -/
theorem exists_kernel_coordinates (hχ : IsMaximalProper χ hG) :
    ∃ r n : ℕ, r ≤ 1 ∧
      ∃ e : Additive (rationalDiscreteValuationImage Mχ) ≃ₗ[ℤ]
        (Fin r → ℤ) × (Fin n → ℤ),
        ∀ x : Additive (rationalDiscreteValuationImage Mχ),
          (e x).2 = 0 ↔ rationalValuationImageMap iχ x.toMul = 1 := by
  let d := fixedLeviParabolicModel hG χ (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
  change ¬ IsIso d.p ∧ _ at hχ
  obtain ⟨T, a, ha⟩ := exists_isSplitComponent Mχ
  have h := exists_maximalLevi_product_coordinates hG d.parabolic d.levi hχ.1 hχ.2 ha
  simpa only [d.comp] using h

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
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

variable
  {DForward DReverse : Set Xχ}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set Xχ} (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

set_option hygiene false in
local notation "jχ" =>
  conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
    p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

include hneForward hDForwardΩ hneReverse hDReverseΩ in
private theorem dense_commonRegular_unitary :
    Dense {z : Uχ | unitaryToUnramified Mχ z ∈ p.regularRegion ∩ q.regularRegion} := by
  have hpd : p.denominator ≠ 0 := fun h0 => hneForward.elim fun w hw =>
    p.denominator_nonzero ⟨w, hDForwardΩ hw⟩ (by rw [h0]; rfl)
  have hqd : q.denominator ≠ 0 := fun h0 => hneReverse.elim fun w hw =>
    q.denominator_nonzero ⟨w, hDReverseΩ hw⟩ (by rw [h0]; rfl)
  let := rationalUnramifiedRegularFunctions_isDomain Mχ hπχ hMχ
  exact (ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero Mχ hMχ
    (p.denominator * q.denominator) (mul_ne_zero hpd hqd)).mono (fun w hw =>
      have hw' : p.denominator.val (unitaryToUnramified Mχ w) *
          q.denominator.val (unitaryToUnramified Mχ w) ≠ 0 := hw
      ⟨left_ne_zero_of_mul hw', right_ne_zero_of_mul hw'⟩)

include hDForward hDReverse hD in
set_option maxHeartbeats 800000 in
/-- Specialization of the bounded ambient-invariant fraction argument to the
actual canonical scalar for a maximal proper dynamic parabolic. -/
theorem inverse_regularAt
    (hχ : IsMaximalProper χ hG)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
    (z : Xχ) (hz : z.val ∈ Uχ) :
    RationalFunctionRegularAt Mχ hπχ hMχ jχ⁻¹ z := by
  obtain ⟨r, n, hr, e, he⟩ := exists_kernel_coordinates χ hG hχ
  obtain ⟨B, hB, hbound⟩ :=
    DynamicOppositeInverseBound.unitaryCommonRegularInverseBounded_of_squareIntegrable
      χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
      hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
  have hfixed (eta : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
      rationalUnramifiedFunctionFieldTranslation Mχ hπχ hMχ
        (rationalUnramifiedCharacterRestrict iχ eta) jχ⁻¹ = jχ⁻¹ := by
    rw [map_inv₀]
    exact congrArg Inv.inv (DynamicOppositeAmbientTwist.conditionalCanonicalRationalScalar_ambient_fixed
      χ hG eta K hK A hRefl hCST hPK hOppK p q hDForward hneForward hDForwardΩ
      hDReverse hneReverse hDReverseΩ hne hi)
  have hb : HasDenseUnitaryNormBound hMχ jχ⁻¹ :=
    ⟨_, dense_commonRegular_unitary χ hG hRefl hCST K hK hPK hOppK A p q
      hneForward hDForwardΩ hneReverse hDReverseΩ,
      B, hB.le, fun w hw => hbound (unitaryToUnramified Mχ w) hw w.property⟩
  exact unitaryRegular_of_ambient_fixed_of_dense_normBound hMχ e hr iχ he jχ⁻¹
    hfixed hb ⟨z.val, hz⟩

end Langlands.Plancherel.DynamicOppositeMaximalLeviRegularity
