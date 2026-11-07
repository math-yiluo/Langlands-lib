import Langlands.Representation.Geometric.RepresentedGeometricLemmaOriginalCorrections

/-! # The represented coefficient character on the original common Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private theorem representedNormalizedCoefficient_units_identity (u v a b c : ℂˣ) :
    u / (a ^ 2 * c ^ 2) * v =
      (v * b⁻¹ * c⁻¹ * (u * a⁻¹ * c⁻¹)) * (b * a⁻¹) := by
  calc
    _ = (u * v) * (a⁻¹ * a⁻¹ * c⁻¹ * c⁻¹) := by
      simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
      ac_rfl
    _ = ((u * v) * (a⁻¹ * a⁻¹ * c⁻¹ * c⁻¹)) * (b⁻¹ * b) := by
      rw [inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance normalizedCharacterAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local instance normalizedCharacterCommonLeviPointTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UI" => pointImage (rQ ≫ q)
local notation "PJ" => pointImage p
local notation "hUI" => isClosed_pointImage_comp q rQ hq.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hPJ" => isClosed_pointImage p hp.isClosedSubgroup
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ
local notation "dJ" => isSemidirectDecomposition_pointImage p l r
  hp.isClosedSubgroup hr hmul
local notation "hMJPJ" => le_trans (IsSemidirectDecomposition.levi_le dJ)
  (fun _ hx => Subgroup.le_normalizer hx)
local notation "eL" => D.targetCommonLeviPointsEquiv.toMonoidHom
local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

/-- The normalized coefficient expression restricted to the original common
Levi, retaining the full original target correction-intersection modulus. -/
def normalizedCommonLeviCoefficientCharacter : rationalPoints D.L' →* ℂˣ :=
  (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardTargetRadicalModulus) /
    Jacquet.complexCharacter
      ((geometricTargetCorrectionIntersectionModulus
        MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL)) *
    Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus)

/-- The positive target endpoint half times the inverse source endpoint half,
both evaluated at the same original target common-Levi point. -/
def normalizedCommonLeviEndpointCharacter : rationalPoints D.L' →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardTargetEndpointModulus) *
    Jacquet.inverseHalfCharacter D.forwardSourceEndpointModulus

/-- The coefficient expression retains the actual original outer target
inverse half, full Haar ratio and original inducing half transported by `D.e`. -/
theorem normalizedCommonLeviCoefficientCharacter_eq_original :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    letI := leviPointTopology D.l' D.hl'
    letI := leviPointTopology D.lQ' D.hlQ'
    D.normalizedCommonLeviCoefficientCharacter =
      (leviInverseHalfCharacter q lQ rQ hq hrQ hlQ).toMonoidHom.comp
          (rationalPoints.map (D.lQ' ≫ D.q')) *
        (Jacquet.complexCharacter D.forwardTargetRadicalModulus /
          Jacquet.complexCharacter
            ((geometricTargetCorrectionIntersectionModulus
              MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL)) *
        (leviInducingHalfCharacter p l r hp hr hl).toMonoidHom.comp
          ((rationalPoints.map (D.l' ≫ D.p')).comp D.e.toMonoidHom) := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  rw [D.targetInverseHalfCharacter_commonLevi, D.inducingHalfCharacter_commonLevi]
  change D.normalizedCommonLeviCoefficientCharacter =
    Jacquet.inverseHalfCharacter D.forwardTargetRadicalModulus *
      (Jacquet.complexCharacter D.forwardTargetRadicalModulus /
        Jacquet.complexCharacter
          ((geometricTargetCorrectionIntersectionModulus
            MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL)) *
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus)
  apply MonoidHom.ext
  intro x
  have hsquare :
      Jacquet.complexCharacter
          (Jacquet.positiveHalfCharacter D.forwardTargetRadicalModulus) x ^ 2 =
        Jacquet.complexCharacter D.forwardTargetRadicalModulus x := by
    simpa only [Jacquet.complexCharacter, MonoidHom.comp_apply, map_pow] using
      congrArg (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        (Jacquet.positiveHalfCharacter_sq D.forwardTargetRadicalModulus x)
  change _ =
    (Jacquet.complexCharacter
        (Jacquet.positiveHalfCharacter D.forwardTargetRadicalModulus) x)⁻¹ *
      (Jacquet.complexCharacter D.forwardTargetRadicalModulus x /
        Jacquet.complexCharacter
          ((geometricTargetCorrectionIntersectionModulus
            MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL) x) *
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus) x
  rw [← hsquare, pow_two]
  simp only [normalizedCommonLeviCoefficientCharacter, MonoidHom.mul_apply,
    MonoidHom.div_apply, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]

/-- The endpoint expression is the product of the actual inner target
inducing half and the actual inner source inverse half transported by `D.e`. -/
theorem normalizedCommonLeviEndpointCharacter_eq_original :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    letI := leviPointTopology D.l' D.hl'
    letI := leviPointTopology D.lQ' D.hlQ'
    D.normalizedCommonLeviEndpointCharacter =
      (leviInducingHalfCharacter D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ').toMonoidHom *
        (leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom.comp
          D.e.toMonoidHom := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  rw [D.targetHalfCharacter_commonLevi, D.sourceInverseHalfCharacter_commonLevi]
  rfl

namespace DynamicRealization

variable (R : D.DynamicRealization)

section Factorization

variable [SecondCountableTopology (rationalPoints G)]

include R in
/-- The coefficient on the entire original common Levi retains exactly the
product of both original epsilon corrections and the endpoint ratio. -/
theorem normalizedCommonLeviCoefficientCharacter_eq_epsilonEndpoints :
    D.normalizedCommonLeviCoefficientCharacter =
      (D.originalSourceCorrectionCharacter * D.originalTargetCorrectionCharacter) *
        D.normalizedCommonLeviEndpointCharacter := by
  unfold normalizedCommonLeviCoefficientCharacter normalizedCommonLeviEndpointCharacter
  rw [R.originalTargetCorrectionIntersectionModulus_eq_mul,
    R.originalSourceCorrectionCharacter_eq_forward,
    R.originalTargetCorrectionCharacter_eq_forward]
  apply MonoidHom.ext
  intro x
  have hsq (δ : rationalPoints D.L' →* ℝ≥0ˣ) :
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ) x ^ 2 =
        Jacquet.complexCharacter δ x := by
    simpa only [Jacquet.complexCharacter, MonoidHom.comp_apply, map_pow] using
      congrArg (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        (Jacquet.positiveHalfCharacter_sq δ x)
  have ha := hsq D.forwardSourceEndpointModulus
  have hc := hsq D.forwardIntersectionModulus
  simp only [forwardSourceCorrectionCharacter, forwardTargetCorrectionCharacter,
    MonoidHom.mul_apply, MonoidHom.div_apply, Jacquet.inverseHalfCharacter,
    MonoidHom.inv_apply, Jacquet.complexCharacter, MonoidHom.comp_apply, map_mul]
  simp only [Jacquet.complexCharacter, MonoidHom.comp_apply] at ha hc
  rw [← ha, ← hc]
  exact representedNormalizedCoefficient_units_identity _ _ _ _ _

end Factorization

section LocalFieldCancellation

variable [ValuativeRel k] [IsNonarchimedeanLocalField k] [Smooth G.X.hom]

local instance normalizedCharacterTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

include R in
/-- Under the retained structural inputs the normalized coefficient is
exactly the original endpoint normalization on the full common Levi. -/
theorem normalizedCommonLeviCoefficientCharacter_eq_endpoints
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    D.normalizedCommonLeviCoefficientCharacter =
      D.normalizedCommonLeviEndpointCharacter := by
  let : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.rationalPoint_secondCountable k G
  rw [R.normalizedCommonLeviCoefficientCharacter_eq_epsilonEndpoints,
    originalCorrectionCharacter_product_eq_one (D := D) (R := R) hroot hinj]
  apply MonoidHom.ext
  intro x
  exact one_mul _

end LocalFieldCancellation

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
