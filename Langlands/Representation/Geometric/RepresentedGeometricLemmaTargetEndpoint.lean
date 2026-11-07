import Langlands.Representation.Geometric.RepresentedGeometricLemmaNormalizedCoefficient

/-! # The original inner target inducing covariance -/

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

local instance targetEndpointAmbientPointTopology :
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

local instance targetEndpointCommonSourceLeviPointTopology :
    TopologicalSpace (rationalPoints D.M') := leviPointTopology D.l' D.hl'
local instance targetEndpointCommonTargetLeviPointTopology :
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
local notation "dInner" => isSemidirectDecomposition_pointImage D.q' D.lQ' D.rQ'
  D.hq'.isClosedSubgroup D.hrQ' D.hmulQ'
local notation "hInnerRad" => isClosed_pointImage_comp D.q' D.rQ' D.hq'.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left D.hrQ'))
local notation "S" => pointImage (D.r' ≫ D.p')
local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The original inner target parabolic has precisely the literal target
intersection as its image under the original outer Levi point equivalence. -/
theorem mem_targetParabolicPoints_leviPointsEquiv (x : rationalPoints L) :
    letI := leviPointTopology lQ hlQ
    x ∈ pointImage D.q' ↔
      leviPointsEquiv q lQ hq hlQ x ∈ Subgroup.subgroupOf K MI := by
  let := leviPointTopology lQ hlQ
  simpa only [D.targetParabolicPoints_eq, geometricTargetIntersection,
    MulEquiv.toMonoidHom_eq_coe] using
      mem_pointImage_leviPointsEquiv (p := q) (l := lQ) (hp := hq) (hl := hlQ) D.q' x

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The original inner target radical has precisely its literal ambient
intersection image under the same original outer Levi point equivalence. -/
theorem mem_targetRadicalPoints_leviPointsEquiv (x : rationalPoints L) :
    letI := leviPointTopology lQ hlQ
    x ∈ pointImage (D.rQ' ≫ D.q') ↔
      leviPointsEquiv q lQ hq hlQ x ∈ Subgroup.subgroupOf Rt MI := by
  let := leviPointTopology lQ hlQ
  simpa only [Category.assoc, D.targetRadicalPoints_eq, geometricTargetIntersection,
    MulEquiv.toMonoidHom_eq_coe] using
      mem_pointImage_leviPointsEquiv (p := q) (l := lQ) (hp := hq) (hl := hlQ)
        (D.rQ' ≫ D.q') x

/-- The original inner target parabolic point image is the full literal
target intersection, with both original subgroup topologies retained. -/
def targetParabolicPointsEquiv :
    letI := leviPointTopology lQ hlQ
    pointImage D.q' ≃ₜ* K := by
  letI := leviPointTopology lQ hlQ
  exact (GroupTransport.subgroupEquiv (leviPointsEquiv q lQ hq hlQ)
    D.mem_targetParabolicPoints_leviPointsEquiv).trans
      (subgroupOfContinuousEquiv (inf_le_left : K ≤ MI))

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem targetParabolicPointsEquiv_apply_coe (a : pointImage D.q') :
    letI := leviPointTopology lQ hlQ
    (D.targetParabolicPointsEquiv a : rationalPoints G) =
      rationalPoints.map (lQ ≫ q) (a : rationalPoints L) := rfl

/-- The original inner target projection valued in the common Levi's own
rational points, before any ambient intersection transport. -/
def originalTargetLeviProjection :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology lQ hlQ
    pointImage D.q' →* rationalPoints D.L' := by
  letI := hlQ.isConnectedReductive.isAffineHom
  letI := leviPointTopology lQ hlQ
  exact (leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ').symm.toMonoidHom.comp (dInner).projection

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The full literal target projection is exactly the original inner target
projection after the original point-image equivalence. -/
theorem targetIntersectionLeviProjection_original (a : pointImage D.q') :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology lQ hlQ
    D.targetIntersectionLeviProjection (D.targetParabolicPointsEquiv a) =
      D.originalTargetLeviProjection a := by
  let := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  let m := D.originalTargetLeviProjection a
  have hm : leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ' m = (dInner).projection a := by
    exact (leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ').apply_symm_apply _
  have hmval : (D.targetLeviPointsEquiv m : rationalPoints G) =
      rationalPoints.map (lQ ≫ q) ((dInner).projection a : rationalPoints L) := by
    have h := congrArg
      (fun b : pointImage (D.lQ' ≫ D.q') =>
        rationalPoints.map (lQ ≫ q) (b : rationalPoints L)) hm
    change rationalPoints.map (lQ ≫ q)
      (rationalPoints.map (D.lQ' ≫ D.q') m) = _ at h
    simpa only [targetLeviPointsEquiv_apply_coe, pointMap_comp_apply] using h
  have hraw : rationalPoints.map (lQ ≫ q)
      (((dInner).projection a : rationalPoints L)⁻¹ * (a : rationalPoints L)) ∈ Rt := by
    obtain ⟨u, hu⟩ := (dInner).projection_inv_mul_mem a
    have hu' : rationalPoints.map (D.rQ' ≫ D.q' ≫ lQ ≫ q) u =
        rationalPoints.map (lQ ≫ q)
          (((dInner).projection a : rationalPoints L)⁻¹ * (a : rationalPoints L)) := by
      simpa only [pointMap_comp_apply] using congrArg (rationalPoints.map (lQ ≫ q)) hu
    have hmem : rationalPoints.map (lQ ≫ q)
        (((dInner).projection a : rationalPoints L)⁻¹ * (a : rationalPoints L)) ∈
          pointImage (D.rQ' ≫ D.q' ≫ lQ ≫ q) := ⟨u, hu'⟩
    simpa only [D.targetRadicalPoints_eq, geometricTargetIntersection,
      MulEquiv.toMonoidHom_eq_coe] using hmem
  have hproj : (dt).projection (D.targetParabolicPointsEquiv a) =
      D.targetLeviPointsEquiv m := by
    apply ((dt).projection_eq_iff _ _).mpr
    have heq :
        (D.targetLeviPointsEquiv m : rationalPoints G)⁻¹ *
            (D.targetParabolicPointsEquiv a : rationalPoints G) =
          rationalPoints.map (lQ ≫ q)
            (((dInner).projection a : rationalPoints L)⁻¹ * (a : rationalPoints L)) := by
      calc
        _ = (rationalPoints.map (lQ ≫ q) ((dInner).projection a : rationalPoints L))⁻¹ *
            rationalPoints.map (lQ ≫ q) (a : rationalPoints L) :=
          congrArg₂ (fun b c : rationalPoints G => b⁻¹ * c)
            hmval (D.targetParabolicPointsEquiv_apply_coe a)
        _ = _ := by simp only [map_mul, map_inv]
    exact (congrArg (fun t : rationalPoints G => t ∈ Rt) heq).mpr hraw
  exact (congrArg D.targetLeviPointsEquiv.symm hproj).trans
    (D.targetLeviPointsEquiv.symm_apply_apply m)

/-- The full target endpoint Haar half is the original inner target
induction half at the same original parabolic point. -/
theorem targetEndpointHalfCharacter_transport (a : pointImage D.q') :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    HaarModulus.closedHalfCharacter (pointImage (D.rQ' ≫ D.q')) hInnerRad
        (pointImage D.q') (dInner).le_normalizer a =
      HaarModulus.closedHalfCharacter Rt hRt K (dt).le_normalizer
        (D.targetParabolicPointsEquiv a) := by
  let := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  let := leviPoints_locallyCompactSpace q lQ hq hlQ
  let := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := (hMI).locallyCompactSpace
  have h := GroupTransport.closedHalfCharacter_transport (leviPointsEquiv q lQ hq hlQ)
    D.mem_targetRadicalPoints_leviPointsEquiv D.mem_targetParabolicPoints_leviPointsEquiv
    ((hRt).preimage continuous_subtype_val) hInnerRad
    (normalizes_subgroupOf (dt).le_normalizer) (dInner).le_normalizer a
  exact h.trans (closedHalfCharacter_subgroupOf hMI hRt inf_le_left inf_le_left
    (dt).le_normalizer _)

variable (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

/-- The actual inducing covariance of the original inner target triple,
on the original normalized source Jacquet object pulled through `D.e`. -/
def originalTargetInducingCoefficient :
    letI := leviPointTopology l hl
    Representation ℂ (pointImage D.q')
      (Jacquet.Localization.Coinvariants A.representation S 1) := by
  letI := hl.isConnectedReductive.isAffineHom
  letI := hlQ.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  letI := leviPoints_locallyCompactSpace p l hp hl
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  letI := leviPoints_locallyCompactSpace q lQ hq hlQ
  letI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let B := SmoothRep.pullback D.e
    ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj A)
  exact inducingRepresentation (dInner) hInnerRad
    (SmoothRep.pullback (leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ').symm B)

/-- Transport of the full endpoint action is exactly the original inner
target normalized inducing covariance, at every original vector class. -/
theorem originalTargetInducingCoefficient_eq_endpoint :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    D.originalTargetInducingCoefficient A =
      (D.originalTargetIntersectionEndpointAction A).comp
        D.targetParabolicPointsEquiv.toMonoidHom := by
  let := hl.isConnectedReductive.isAffineHom
  let := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let := leviPoints_locallyCompactSpace p l hp hl
  let := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPoints_locallyCompactSpace q lQ hq hlQ
  let := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  ext a x
  exact congrArg₂
    (fun (c : ℂˣ) (m : rationalPoints D.L') =>
      (c : ℂ) •
        (((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj A).representation
          (D.e m) (Jacquet.Localization.mk A.representation S 1 x)))
    (D.targetEndpointHalfCharacter_transport a)
    (D.targetIntersectionLeviProjection_original a).symm

namespace DynamicRealization

variable [ValuativeRel k] [IsNonarchimedeanLocalField k] [Smooth G.X.hom]
  (R : D.DynamicRealization)

local instance targetEndpointTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

/-- Conditional coefficient comparison with the actual original target
inducing covariance, preserving the original ordinary source vector classes. -/
def originalTargetInducingCoefficientEquiv
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    Representation.Equiv ((D.normalizedTargetIntersectionCoefficientAction A).comp
        D.targetParabolicPointsEquiv.toMonoidHom)
      (D.originalTargetInducingCoefficient A) := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  apply equivOfRepresentationEq
  rw [normalizedTargetIntersectionCoefficientAction_eq_endpoints
      (D := D) (A := A) (R := R) hroot hinj,
    ← D.originalTargetInducingCoefficient_eq_endpoint A]

@[simp]
theorem originalTargetInducingCoefficientEquiv_mk
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom))
    (a : letI := leviPointTopology l hl; A) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    originalTargetInducingCoefficientEquiv (D := D) (A := A) (R := R) hroot hinj
        (Jacquet.Localization.mk A.representation S 1 a) =
      Jacquet.Localization.mk A.representation S 1 a := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  rfl

/-- The original-target coefficient equivalence commutes with every source
morphism on the actual original source Jacquet quotient maps. -/
theorem originalTargetInducingCoefficientEquiv_natural
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom))
    {B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (f : A ⟶ B)
    (x : letI := leviPointTopology l hl; Jacquet.Localization.Coinvariants A.representation S 1) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    originalTargetInducingCoefficientEquiv (D := D) (A := B) (R := R) hroot hinj
        (Jacquet.Localization.mapLinear S 1 (SmoothRep.hom f) x) =
      Jacquet.Localization.mapLinear S 1 (SmoothRep.hom f)
        (originalTargetInducingCoefficientEquiv (D := D) (A := A) (R := R) hroot hinj x) := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  rfl

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
