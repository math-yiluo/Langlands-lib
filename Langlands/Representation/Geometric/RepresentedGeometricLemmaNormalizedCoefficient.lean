import Langlands.Representation.Geometric.RepresentedGeometricLemmaCharacterInflation
import Langlands.Representation.Geometric.RepresentedGeometricLemmaSourceJacquet
import Langlands.Representation.Twist.PullbackProof
import Langlands.Representation.Category.Twist

/-! # Actual source Jacquet actions and the full-intersection coefficient -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance normalizedCoefficientAmbientPointTopology :
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

local instance normalizedCoefficientCommonSourceLeviPointTopology :
    TopologicalSpace (rationalPoints D.M') := leviPointTopology D.l' D.hl'
local instance normalizedCoefficientCommonTargetLeviPointTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UJ" => pointImage (r ≫ p)
local notation "PJ" => pointImage p
local notation "K" => geometricTargetIntersection MI PJ z⁻¹
local notation "Rt" => geometricTargetIntersection MI UJ z⁻¹
local notation "dt" => D.targetPoints_isSemidirectDecomposition
local notation "hMI" => isClosed_leviPoints q lQ hq hlQ
local notation "hUJ" => isClosed_pointImage_comp p r hp.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hr))
local notation "hRt" => isClosed_geometricTargetIntersection MI UJ hMI hUJ z⁻¹
local notation "S" => pointImage (D.r' ≫ D.p')
local notation "Hs" => pointImage (D.l' ≫ D.p')
local notation "hHsS" => pointImage_le_normalizer D.p' D.l' D.r' D.hr'
local notation "eM" => MonoidHom.rangeRestrict (rationalPoints.map (D.l' ≫ D.p'))
local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

variable (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

/-- The ordinary source-intersection Jacquet action, pulled to the original
target common Levi through the actual map `D.e`. -/
def ordinaryCommonLeviCoefficientAction :
    letI := leviPointTopology l hl
    Representation ℂ (rationalPoints D.L')
      (Jacquet.Localization.Coinvariants A.representation S 1) := by
  letI := leviPointTopology l hl
  exact (Jacquet.Localization.action A.representation S 1 Hs hHsS
    (Jacquet.Localization.isInvariant_one S Hs hHsS)).comp
      (MonoidHom.comp eM D.e.toMonoidHom)

/-- The scalar-normalized coefficient on the actual ordinary source Jacquet
carrier and the full literal target intersection. -/
def normalizedTargetIntersectionCoefficientAction :
    letI := leviPointTopology l hl
    Representation ℂ K (Jacquet.Localization.Coinvariants A.representation S 1) := by
  letI := leviPointTopology l hl
  exact Langlands.twist D.normalizedTargetIntersectionCoefficientCharacter
    ((D.ordinaryCommonLeviCoefficientAction A).comp D.targetIntersectionLeviProjection)

/-- The actual inner normalized source Jacquet action pulled through `D.e`
and the original target projection, with the full original target endpoint half. -/
def originalTargetIntersectionEndpointAction :
    letI := leviPointTopology l hl
    Representation ℂ K (Jacquet.Localization.Coinvariants A.representation S 1) := by
  letI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPoints_locallyCompactSpace p l hp hl
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  exact Langlands.twist (HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer)
    ((((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj A).representation).comp
      (D.e.toMonoidHom.comp D.targetIntersectionLeviProjection))

/-- The original normalized source Jacquet action has exactly its original
transported endpoint inverse half on the ordinary source Jacquet carrier. -/
theorem normalizedSourceJacquetAction_eq :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    (((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj A).representation).comp
        D.e.toMonoidHom =
      Langlands.twist (Jacquet.inverseHalfCharacter D.forwardSourceEndpointModulus)
        (D.ordinaryCommonLeviCoefficientAction A) := by
  let := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPoints_locallyCompactSpace p l hp hl
  let := leviPoints_nonarchimedeanGroup p l hp hl
  change Langlands.twist
    ((leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom.comp D.e.toMonoidHom)
    (D.ordinaryCommonLeviCoefficientAction A) = _
  rw [D.sourceInverseHalfCharacter_commonLevi]
  rfl

/-- The actual inner endpoint coefficient is the full endpoint-character twist
of the original ordinary source Jacquet action. -/
theorem originalTargetIntersectionEndpointAction_eq :
    letI := leviPointTopology l hl
    D.originalTargetIntersectionEndpointAction A =
      Langlands.twist D.normalizedTargetIntersectionEndpointCharacter
        ((D.ordinaryCommonLeviCoefficientAction A).comp D.targetIntersectionLeviProjection) := by
  let := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPoints_locallyCompactSpace p l hp hl
  let := leviPoints_nonarchimedeanGroup p l hp hl
  change Langlands.twist (HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer)
    (((((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj A).representation).comp
      D.e.toMonoidHom).comp D.targetIntersectionLeviProjection) = _
  rw [D.normalizedSourceJacquetAction_eq A, Langlands.twist_comp, Langlands.twist_twist]
  rfl

namespace DynamicRealization

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (R : D.DynamicRealization)

include R in
/-- The exact original epsilon product is the only remaining twist between
these full-intersection actions on the same actual Jacquet quotient. -/
theorem normalizedTargetIntersectionCoefficientAction_eq_epsilonTwist
    [SecondCountableTopology (rationalPoints G)] :
    letI := leviPointTopology l hl
    D.normalizedTargetIntersectionCoefficientAction A =
      Langlands.twist
        ((D.originalSourceCorrectionCharacter * D.originalTargetCorrectionCharacter).comp
          D.targetIntersectionLeviProjection)
        (D.originalTargetIntersectionEndpointAction A) := by
  let := leviPointTopology l hl
  rw [D.originalTargetIntersectionEndpointAction_eq A, Langlands.twist_twist]
  unfold normalizedTargetIntersectionCoefficientAction
  rw [normalizedTargetIntersectionCoefficientCharacter_eq_epsilonEndpoints (D := D) (R := R)]

section Cancellation

variable [Smooth G.X.hom]

local instance normalizedCoefficientTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

include R in
/-- Conditional equality with the actual normalized inner Jacquet endpoint
action at every point of the full literal target intersection. -/
theorem normalizedTargetIntersectionCoefficientAction_eq_endpoints
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    letI := leviPointTopology l hl
    D.normalizedTargetIntersectionCoefficientAction A =
      D.originalTargetIntersectionEndpointAction A := by
  let := leviPointTopology l hl
  rw [D.originalTargetIntersectionEndpointAction_eq A]
  unfold normalizedTargetIntersectionCoefficientAction
  rw [normalizedTargetIntersectionCoefficientCharacter_eq_endpoints (D := D) (R := R) hroot hinj]

/-- The coefficient comparison is the identity on original vector classes. -/
def normalizedTargetIntersectionCoefficientEquiv
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    letI := leviPointTopology l hl
    (D.normalizedTargetIntersectionCoefficientAction A).Equiv
      (D.originalTargetIntersectionEndpointAction A) := by
  letI := leviPointTopology l hl
  exact equivOfRepresentationEq
    (normalizedTargetIntersectionCoefficientAction_eq_endpoints (D := D) (A := A) (R := R)
      hroot hinj)

@[simp]
theorem normalizedTargetIntersectionCoefficientEquiv_mk
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom))
    (a : letI := leviPointTopology l hl; A) :
    letI := leviPointTopology l hl
    normalizedTargetIntersectionCoefficientEquiv (D := D) (A := A) (R := R) hroot hinj
        (Jacquet.Localization.mk A.representation S 1 a) =
      Jacquet.Localization.mk A.representation S 1 a := by
  let := leviPointTopology l hl
  rfl

/-- The identity-on-classes comparison commutes with every original source
intertwiner, without a representation-finiteness condition. -/
theorem normalizedTargetIntersectionCoefficientEquiv_natural
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom))
    {B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)} (f : A ⟶ B)
    (x : letI := leviPointTopology l hl; Jacquet.Localization.Coinvariants A.representation S 1) :
    letI := leviPointTopology l hl
    normalizedTargetIntersectionCoefficientEquiv (D := D) (A := B) (R := R) hroot hinj
        (Jacquet.Localization.mapLinear S 1 (SmoothRep.hom f) x) =
      Jacquet.Localization.mapLinear S 1 (SmoothRep.hom f)
        (normalizedTargetIntersectionCoefficientEquiv (D := D) (A := A) (R := R)
          hroot hinj x) := by
  let := leviPointTopology l hl
  rfl

end Cancellation

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
