import Langlands.Representation.Geometric.RepresentedGeometricLemmaNormalizedCharacter
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups

/-! # Normalized characters on the full represented target intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance characterInflationAmbientPointTopology :
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

local instance characterInflationCommonLeviPointTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UI" => pointImage (rQ ≫ q)
local notation "UJ" => pointImage (r ≫ p)
local notation "PJ" => pointImage p
local notation "K" => geometricTargetIntersection MI PJ z⁻¹
local notation "Lt" => geometricTargetIntersection MI MJ z⁻¹
local notation "Rt" => geometricTargetIntersection MI UJ z⁻¹
local notation "C" => geometricTargetIntersection UI PJ z⁻¹
local notation "dt" => D.targetPoints_isSemidirectDecomposition
local notation "hMI" => isClosed_leviPoints q lQ hq hlQ
local notation "hUI" => isClosed_pointImage_comp q rQ hq.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hUJ" => isClosed_pointImage_comp p r hp.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hr))
local notation "hPJ" => isClosed_pointImage p hp.isClosedSubgroup
local notation "hK" => isClosed_geometricTargetIntersection MI PJ hMI hPJ z⁻¹
local notation "hRt" => isClosed_geometricTargetIntersection MI UJ hMI hUJ z⁻¹
local notation "hC" => isClosed_geometricTargetIntersection UI PJ hUI hPJ z⁻¹
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ
local notation "hKUI" => le_trans (inf_le_left : K ≤ MI) hMIUI
local notation "hKC" => geometricCommonLevi_normalizes_intersection MI PJ UI PJ z⁻¹
  hMIUI (fun _ hx => Subgroup.le_normalizer hx)
local notation "dJ" => isSemidirectDecomposition_pointImage p l r
  hp.isClosedSubgroup hr hmul
local notation "hMJPJ" => le_trans (IsSemidirectDecomposition.levi_le dJ)
  (fun _ hx => Subgroup.le_normalizer hx)
local notation "eL" => D.targetCommonLeviPointsEquiv.toMonoidHom
local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

/-- The original common Levi included in the full literal target intersection. -/
def targetCommonLeviInIntersection : rationalPoints D.L' →* K :=
  (Subgroup.inclusion (dt).levi_le).comp D.targetLeviPointsEquiv.toMonoidHom

/-- The original target semidirect projection, valued in its own common Levi. -/
def targetIntersectionLeviProjection : K →* rationalPoints D.L' :=
  D.targetLeviPointsEquiv.symm.toMonoidHom.comp (dt).projection

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem targetIntersectionLeviProjection_commonLevi (x : rationalPoints D.L') :
    D.targetIntersectionLeviProjection (D.targetCommonLeviInIntersection x) = x := by
  change D.targetLeviPointsEquiv.symm
    ((dt).projection (Subgroup.inclusion (dt).levi_le (D.targetLeviPointsEquiv x))) = x
  exact (congrArg D.targetLeviPointsEquiv.symm
    ((dt).projection_levi (D.targetLeviPointsEquiv x))).trans
      (D.targetLeviPointsEquiv.symm_apply_apply x)

/-- The original target-radical modulus on the entire literal intersection. -/
def targetIntersectionRadicalModulus
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) : K →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter UI hUI K hKUI

/-- The full original correction-intersection modulus on that same group. -/
def targetIntersectionCorrectionModulus
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) : K →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter C hC K hKC

theorem targetIntersectionRadicalModulus_commonLevi :
    D.targetIntersectionRadicalModulus.comp D.targetCommonLeviInIntersection =
      D.forwardTargetRadicalModulus := by
  apply MonoidHom.ext
  intro x
  rfl

theorem targetIntersectionCorrectionModulus_commonLevi :
    D.targetIntersectionCorrectionModulus.comp D.targetCommonLeviInIntersection =
      (geometricTargetCorrectionIntersectionModulus
        MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL := by
  apply MonoidHom.ext
  intro x
  symm
  apply geometricTargetCorrectionIntersectionModulus_eq_ambient
    MI MJ UI PJ z⁻¹ hUI hPJ hMIUI hMJPJ
    (D.targetCommonLeviPointsEquiv x)
  rfl

/-- The full-intersection scalar expression, with the original radical half,
full correction modulus and the source half through the actual projection. -/
def normalizedTargetIntersectionCoefficientCharacter : K →* ℂˣ :=
  (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.targetIntersectionRadicalModulus) /
    Jacquet.complexCharacter D.targetIntersectionCorrectionModulus) *
      (Jacquet.complexCharacter
        (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus)).comp
          D.targetIntersectionLeviProjection

/-- The full original target endpoint half times the source endpoint inverse
half transported through the original target projection. -/
def normalizedTargetIntersectionEndpointCharacter : K →* ℂˣ :=
  HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer *
    (Jacquet.inverseHalfCharacter D.forwardSourceEndpointModulus).comp
      D.targetIntersectionLeviProjection

theorem normalizedTargetIntersectionCoefficientCharacter_commonLevi :
    D.normalizedTargetIntersectionCoefficientCharacter.comp D.targetCommonLeviInIntersection =
      D.normalizedCommonLeviCoefficientCharacter := by
  apply MonoidHom.ext
  intro x
  have hu := congrArg (fun f : rationalPoints D.L' →* ℝ≥0ˣ => f x)
    D.targetIntersectionRadicalModulus_commonLevi
  have hd := congrArg (fun f : rationalPoints D.L' →* ℝ≥0ˣ => f x)
    D.targetIntersectionCorrectionModulus_commonLevi
  change (Jacquet.complexCharacter
      (Jacquet.positiveHalfCharacter D.targetIntersectionRadicalModulus)
        (D.targetCommonLeviInIntersection x) /
    Jacquet.complexCharacter D.targetIntersectionCorrectionModulus
      (D.targetCommonLeviInIntersection x)) *
        Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus)
          (D.targetIntersectionLeviProjection (D.targetCommonLeviInIntersection x)) = _
  rw [D.targetIntersectionLeviProjection_commonLevi]
  simp only [MonoidHom.comp_apply] at hu hd
  simp only [normalizedCommonLeviCoefficientCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.mul_apply, MonoidHom.div_apply,
    MonoidHom.comp_apply, hu, hd]

/-- Restriction of the full endpoint character retains the previously
identified actual inner endpoint characters on the original common Levi. -/
theorem normalizedTargetIntersectionEndpointCharacter_commonLevi :
    D.normalizedTargetIntersectionEndpointCharacter.comp D.targetCommonLeviInIntersection =
      D.normalizedCommonLeviEndpointCharacter := by
  apply MonoidHom.ext
  intro x
  change HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer
      (D.targetCommonLeviInIntersection x) *
    Jacquet.inverseHalfCharacter D.forwardSourceEndpointModulus
      (D.targetIntersectionLeviProjection (D.targetCommonLeviInIntersection x)) = _
  rw [D.targetIntersectionLeviProjection_commonLevi]
  rfl

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Every character trivial on the original intersection radical inflates
from its restriction to the original common Levi through its original projection. -/
theorem targetIntersectionCharacter_eq_projection
    {A : Type*} [Group A] (χ : K →* A)
    (hχ : ∀ r : Subgroup.subgroupOf Rt K, χ (r : K) = 1) :
    χ = (χ.comp D.targetCommonLeviInIntersection).comp D.targetIntersectionLeviProjection := by
  apply MonoidHom.ext
  intro x
  have hr :
      ((D.targetCommonLeviInIntersection (D.targetIntersectionLeviProjection x))⁻¹ * x : K) ∈
        Subgroup.subgroupOf Rt K := by
    change ((D.targetLeviPointsEquiv
      (D.targetLeviPointsEquiv.symm ((dt).projection x)) : rationalPoints G)⁻¹ *
        (x : rationalPoints G)) ∈ Rt
    rw [D.targetLeviPointsEquiv.apply_symm_apply]
    exact (dt).projection_inv_mul_mem x
  have h := hχ ⟨_, hr⟩
  change χ ((D.targetCommonLeviInIntersection (D.targetIntersectionLeviProjection x))⁻¹ * x) = 1 at h
  rw [map_mul, map_inv] at h
  exact (inv_mul_eq_one.mp h).symm

section LocalFieldInflation

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

include D in
omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Compact-subgroup containment for the literal target intersection radical
comes directly from the supplied represented radical. -/
theorem targetIntersectionRadical_isLimitOfCompactSubgroups :
    Jacquet.Localization.IsLimitOfCompactSubgroups Rt := by
  simpa only [Category.assoc, D.targetRadicalPoints_eq, geometricTargetIntersection,
    MulEquiv.toMonoidHom_eq_coe] using
    isLimitOfCompactSubgroups_pointImage_radical (D.q' ≫ lQ ≫ q) D.rQ'
      (D.hq'.isClosedSubgroup.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup)) D.hrQ'.1

/-- Both remaining positive moduli are trivial on the full target radical,
and the source half is trivial there through the actual projection. -/
theorem normalizedTargetIntersectionCoefficientCharacter_eq_one_on_radical
    (r : Subgroup.subgroupOf Rt K) :
    D.normalizedTargetIntersectionCoefficientCharacter (r : K) = 1 := by
  have hc := isLimitOfCompactSubgroups_subgroupOf Rt K hK
    D.targetIntersectionRadical_isLimitOfCompactSubgroups
  have hu := positiveCharacter_eq_one_on_compactLimit D.targetIntersectionRadicalModulus
    (HaarModulus.isOpen_ker_closedRestrictCharacter UI hUI K hKUI) (Subgroup.subgroupOf Rt K) hc r
  have hd := positiveCharacter_eq_one_on_compactLimit D.targetIntersectionCorrectionModulus
    (HaarModulus.isOpen_ker_closedRestrictCharacter C hC K hKC) (Subgroup.subgroupOf Rt K) hc r
  have hp : D.targetIntersectionLeviProjection (r : K) = 1 := by
    change D.targetLeviPointsEquiv.symm ((dt).projection (r : K)) = 1
    rw [((dt).projection_eq_one_iff _).mpr r.property, map_one]
  simp only [normalizedTargetIntersectionCoefficientCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.mul_apply, MonoidHom.div_apply,
    MonoidHom.comp_apply, hu, hd, hp, map_one, div_one, mul_one]

/-- The exact coefficient on the whole literal target intersection is inflated
from the coefficient already calculated on the entire original common Levi. -/
theorem normalizedTargetIntersectionCoefficientCharacter_eq_projection :
    D.normalizedTargetIntersectionCoefficientCharacter =
      D.normalizedCommonLeviCoefficientCharacter.comp D.targetIntersectionLeviProjection := by
  rw [D.targetIntersectionCharacter_eq_projection
    D.normalizedTargetIntersectionCoefficientCharacter
    D.normalizedTargetIntersectionCoefficientCharacter_eq_one_on_radical,
    D.normalizedTargetIntersectionCoefficientCharacter_commonLevi]

/-- The original full target endpoint half is trivial on its radical;
the source endpoint factor is trivial there through the actual projection. -/
theorem normalizedTargetIntersectionEndpointCharacter_eq_one_on_radical
    (r : Subgroup.subgroupOf Rt K) :
    D.normalizedTargetIntersectionEndpointCharacter (r : K) = 1 := by
  have hp : (dt).projection (r : K) = 1 :=
    ((dt).projection_eq_one_iff _).mpr r.property
  have hown : D.targetIntersectionLeviProjection (r : K) = 1 := by
    change D.targetLeviPointsEquiv.symm ((dt).projection (r : K)) = 1
    rw [hp, map_one]
  have ht := closedHalfCharacter_eq_comp_projection (dt) hRt
    (isUnimodularModulus_of_isLimitOfCompactSubgroups Rt hRt
      D.targetIntersectionRadical_isLimitOfCompactSubgroups)
  change HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer (r : K) *
    Jacquet.inverseHalfCharacter D.forwardSourceEndpointModulus
      (D.targetIntersectionLeviProjection (r : K)) = 1
  have hhalf : HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer (r : K) = 1 := by
    exact (congrArg (fun f : K →* ℂˣ => f (r : K)) ht).trans
      ((congrArg (HaarModulus.closedHalfCharacter Rt hRt Lt (dt).levi_le_normalizer)
        hp).trans (map_one _))
  rw [hhalf, hown, map_one, mul_one]

/-- The full endpoint normalization is inflated from its actual common-Levi
restriction, using unimodularity of the original represented radical. -/
theorem normalizedTargetIntersectionEndpointCharacter_eq_projection :
    D.normalizedTargetIntersectionEndpointCharacter =
      D.normalizedCommonLeviEndpointCharacter.comp D.targetIntersectionLeviProjection := by
  rw [D.targetIntersectionCharacter_eq_projection
    D.normalizedTargetIntersectionEndpointCharacter
    D.normalizedTargetIntersectionEndpointCharacter_eq_one_on_radical,
    D.normalizedTargetIntersectionEndpointCharacter_commonLevi]

namespace DynamicRealization

variable (R : D.DynamicRealization)

include R in
/-- Both original epsilon corrections account for the full discrepancy
between coefficient and endpoint characters on the whole literal intersection. -/
theorem normalizedTargetIntersectionCoefficientCharacter_eq_epsilonEndpoints
    [SecondCountableTopology (rationalPoints G)] :
    D.normalizedTargetIntersectionCoefficientCharacter =
      (D.originalSourceCorrectionCharacter * D.originalTargetCorrectionCharacter).comp
          D.targetIntersectionLeviProjection *
        D.normalizedTargetIntersectionEndpointCharacter := by
  rw [D.normalizedTargetIntersectionCoefficientCharacter_eq_projection,
    normalizedCommonLeviCoefficientCharacter_eq_epsilonEndpoints (D := D) (R := R),
    MonoidHom.mul_comp, ← D.normalizedTargetIntersectionEndpointCharacter_eq_projection]

section LocalFieldCancellation

variable [Smooth G.X.hom]

local instance characterInflationTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

include R in
/-- Under the retained structural inputs the exact full-intersection
coefficient equals the original endpoint normalization on every point. -/
theorem normalizedTargetIntersectionCoefficientCharacter_eq_endpoints
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    D.normalizedTargetIntersectionCoefficientCharacter =
      D.normalizedTargetIntersectionEndpointCharacter := by
  rw [D.normalizedTargetIntersectionCoefficientCharacter_eq_projection,
    normalizedCommonLeviCoefficientCharacter_eq_endpoints (D := D) (R := R) hroot hinj,
    ← D.normalizedTargetIntersectionEndpointCharacter_eq_projection]

end LocalFieldCancellation

end DynamicRealization

end LocalFieldInflation

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
