import Langlands.Representation.Geometric.RepresentedGeometricLemmaHaarBalance
import Langlands.Representation.Geometric.RepresentedGeometricLemmaEndpointCharacters
import Langlands.Representation.Aubert.General.DynamicProjection
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # Original epsilon corrections for represented intersections -/

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

local instance originalCorrectionsAmbientPointTopology :
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

local instance originalCorrectionsCommonLeviPointTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "PI" => pointImage q
local notation "PJ" => pointImage p
local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UI" => pointImage (rQ ≫ q)
local notation "UJ" => pointImage (r ≫ p)
local notation "hPI" => isClosed_pointImage q hq.isClosedSubgroup
local notation "hPJ" => isClosed_pointImage p hp.isClosedSubgroup
local notation "hMI" => isClosed_leviPoints q lQ hq hlQ
local notation "hMJ" => isClosed_leviPoints p l hp hl
local notation "hUI" => isClosed_pointImage_comp q rQ hq.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hUJ" => isClosed_pointImage_comp p r hp.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hr))
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ
local notation "hMJUJ" => pointImage_le_normalizer p l r hr
local notation "dI" => isSemidirectDecomposition_pointImage q lQ rQ
  hq.isClosedSubgroup hrQ hmulQ
local notation "hMIPI" => le_trans (IsSemidirectDecomposition.levi_le dI)
  (fun _ hx => Subgroup.le_normalizer hx)
local notation "dJ" => isSemidirectDecomposition_pointImage p l r
  hp.isClosedSubgroup hr hmul
local notation "hMJPJ" => le_trans (IsSemidirectDecomposition.levi_le dJ)
  (fun _ hx => Subgroup.le_normalizer hx)
local notation "eL" => D.targetCommonLeviPointsEquiv.toMonoidHom
local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q
local notation "flat" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe
  (inf_le_left : geometricTargetIntersection MI MJ z⁻¹ ≤ MI))
local notation "pz" => p ≫ Iso.hom (G.innerIso z⁻¹)
local notation "hpz" => IsParabolicSubgroup.comp_iso hp (G.innerIso z⁻¹)
local notation "dZ" => isSemidirectDecomposition_pointImage pz l r
  (IsParabolicSubgroup.isClosedSubgroup hpz) hr hmul

/-- The original source epsilon correction pulled back to the actual common Levi. -/
def originalSourceCorrectionCharacter : rationalPoints D.L' →* ℂˣ :=
  (geometricSourceCorrectionCharacter MI MJ z⁻¹ PI UJ hUJ hPI hMJUJ hMIPI).comp eL

/-- The original target epsilon correction pulled back to the same actual Levi. -/
def originalTargetCorrectionCharacter : rationalPoints D.L' →* ℂˣ :=
  (geometricTargetCorrectionCharacter MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL

namespace DynamicRealization

variable (R : D.DynamicRealization)

include R in
omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The original target Levi projection preserves the forward source radical. -/
theorem targetProjection_mem_sourceRadical
    (a : PI) (ha : (a : rationalPoints G) ∈
      (UJ).map (MulAut.conj z⁻¹).toMonoidHom) :
    ((dI).projection a : rationalPoints G) ∈
      (UJ).map (MulAut.conj z⁻¹).toMonoidHom := by
  have hP : PI =
      (Dynamic.parabolic (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetParabolic]
  have hM : MI =
      (Dynamic.centralizer (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetLevi]
  have hU : UI =
      (Dynamic.unipotent (CommGroupScheme.groupHom R.targetCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.targetRadical]
  rw [← R.haarSourceRadicalPoints_eq] at ha ⊢
  exact (dI).projection_mem_commonTorusUnipotent iT
    R.targetCocharacter R.sourceCocharacter hP hM hU a ha

include R in
omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The actual inverse-conjugated source projection preserves the target radical. -/
theorem sourceProjection_mem_targetRadical
    (a : pointImage pz) (ha : (a : rationalPoints G) ∈ UI) :
    ((dZ).projection a : rationalPoints G) ∈ UI := by
  have hP : pointImage pz =
      (Dynamic.parabolic (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier, R.sourceParabolic]
  have hM : pointImage (l ≫ pz) =
      (Dynamic.centralizer (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier]
    exact congrArg SubgroupFunctor.rationalPoints R.sourceLevi
  have hU : pointImage (r ≫ pz) =
      (Dynamic.unipotent (CommGroupScheme.groupHom R.sourceCocharacter ≫ iT)).rationalPoints := by
    rw [pointImage_eq_range_carrier]
    exact congrArg SubgroupFunctor.rationalPoints R.sourceRadical
  rw [← R.haarTargetRadicalPoints_eq] at ha ⊢
  exact (dZ).projection_mem_commonTorusUnipotent iT
    R.sourceCocharacter R.targetCocharacter hP hM hU a ha

section Factorization

variable [SecondCountableTopology (rationalPoints G)]

include R in
/-- The source correction subgroup has the actual target endpoint and common
radical as its two Haar factors on the original common Levi. -/
theorem originalSourceCorrectionIntersectionModulus_eq_mul :
    (geometricSourceCorrectionIntersectionModulus
        MI MJ z⁻¹ PI UJ hUJ hPI hMJUJ hMIPI).comp eL =
      D.forwardTargetEndpointModulus * D.forwardIntersectionModulus := by
  rw [geometricSourceCorrectionIntersectionModulus_eq_forward]
  have h := (dI).interOfProjection_closedRestrictCharacter
    ((UJ).map (MulAut.conj z⁻¹).toMonoidHom) R.targetProjection_mem_sourceRadical
    (continuous_projection_pointImage q lQ rQ hq hlQ hrQ hmulQ)
    hPI hMI hUI (isClosed_map_conj UJ hUJ z⁻¹)
    (geometricTargetIntersection MI MJ z⁻¹)
    (le_trans inf_le_left hMIPI)
    (le_trans inf_le_left (fun _ hx => Subgroup.le_normalizer hx))
    (le_trans inf_le_left hMIUI)
    (le_trans inf_le_right
      (le_trans (Subgroup.map_mono hMJUJ) (Subgroup.le_normalizer_map _)))
  apply MonoidHom.ext
  intro x
  exact congrArg
    (fun f : geometricTargetIntersection MI MJ z⁻¹ →* ℝ≥0ˣ => f (flat (eL x))) h

include R in
/-- The target correction subgroup has the original source endpoint and common
radical as its two Haar factors at the same original common-Levi point. -/
theorem originalTargetCorrectionIntersectionModulus_eq_mul :
    (geometricTargetCorrectionIntersectionModulus
        MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL =
      D.forwardSourceEndpointModulus * D.forwardIntersectionModulus := by
  rw [geometricTargetCorrectionIntersectionModulus_eq_forward]
  have hPz : pointImage pz = (PJ).map (MulAut.conj z⁻¹).toMonoidHom :=
    rationalPoints_range_comp_innerIso p z⁻¹
  have hMz : pointImage (l ≫ pz) = (MJ).map (MulAut.conj z⁻¹).toMonoidHom := by
    simpa only [Category.assoc] using rationalPoints_range_comp_innerIso (l ≫ p) z⁻¹
  have hUz : pointImage (r ≫ pz) = (UJ).map (MulAut.conj z⁻¹).toMonoidHom := by
    simpa only [Category.assoc] using rationalPoints_range_comp_innerIso (r ≫ p) z⁻¹
  have hSP : geometricTargetIntersection MI MJ z⁻¹ ≤
      Subgroup.normalizer (pointImage pz) := by
    rw [hPz]
    exact le_trans inf_le_right
      (le_trans (Subgroup.map_mono hMJPJ) (Subgroup.le_normalizer_map _))
  have hSM : geometricTargetIntersection MI MJ z⁻¹ ≤
      Subgroup.normalizer (pointImage (l ≫ pz)) := by
    rw [hMz]
    exact le_trans inf_le_right (fun _ hx => Subgroup.le_normalizer hx)
  have hSU : geometricTargetIntersection MI MJ z⁻¹ ≤
      Subgroup.normalizer (pointImage (r ≫ pz)) := by
    rw [hUz]
    exact le_trans inf_le_right
      (le_trans (Subgroup.map_mono hMJUJ) (Subgroup.le_normalizer_map _))
  have h := (dZ).interOfProjection_closedRestrictCharacter UI
    R.sourceProjection_mem_targetRadical
    (continuous_projection_pointImage pz l r hpz hl hr hmul)
    (isClosed_pointImage pz (IsParabolicSubgroup.isClosedSubgroup hpz))
    (isClosed_leviPoints pz l hpz hl)
    (isClosed_pointImage_comp pz r (IsParabolicSubgroup.isClosedSubgroup hpz)
      (IsUnipotentRadical.isClosedSubgroup (And.left hr)))
    hUI (geometricTargetIntersection MI MJ z⁻¹) hSP hSM hSU
    (le_trans inf_le_left hMIUI)
  simp only [hPz, hMz, hUz,
    inf_comm ((PJ).map (MulAut.conj z⁻¹).toMonoidHom) UI,
    inf_comm ((MJ).map (MulAut.conj z⁻¹).toMonoidHom) UI,
    inf_comm ((UJ).map (MulAut.conj z⁻¹).toMonoidHom) UI] at h
  apply MonoidHom.ext
  intro x
  exact congrArg
    (fun f : geometricTargetIntersection MI MJ z⁻¹ →* ℝ≥0ˣ => f (flat (eL x))) h

include R in
/-- The original source epsilon equals its factorized forward expression on
all points of the original common Levi. -/
theorem originalSourceCorrectionCharacter_eq_forward :
    D.originalSourceCorrectionCharacter = D.forwardSourceCorrectionCharacter := by
  unfold originalSourceCorrectionCharacter
  rw [geometricSourceCorrectionCharacter_eq,
    geometricSourceCorrectionRadicalModulus_eq_forward]
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus) *
    Jacquet.inverseHalfCharacter
      ((geometricSourceCorrectionIntersectionModulus
        MI MJ z⁻¹ PI UJ hUJ hPI hMJUJ hMIPI).comp eL) = _
  rw [R.originalSourceCorrectionIntersectionModulus_eq_mul]
  apply MonoidHom.ext
  intro x
  simp only [forwardSourceCorrectionCharacter, Jacquet.inverseHalfCharacter,
    Jacquet.complexCharacter, Jacquet.positiveHalfCharacter, MonoidHom.comp_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv, mul_assoc]

include R in
/-- The original target epsilon equals its factorized forward expression at
the same original common-Levi point. -/
theorem originalTargetCorrectionCharacter_eq_forward :
    D.originalTargetCorrectionCharacter = D.forwardTargetCorrectionCharacter := by
  unfold originalTargetCorrectionCharacter
  rw [geometricTargetCorrectionCharacter_eq]
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardTargetRadicalModulus) *
    Jacquet.inverseHalfCharacter
      ((geometricTargetCorrectionIntersectionModulus
        MI MJ z⁻¹ UI PJ hUI hPJ hMIUI hMJPJ).comp eL) = _
  rw [R.originalTargetCorrectionIntersectionModulus_eq_mul]
  apply MonoidHom.ext
  intro x
  simp only [forwardTargetCorrectionCharacter, Jacquet.inverseHalfCharacter,
    Jacquet.complexCharacter, Jacquet.positiveHalfCharacter, MonoidHom.comp_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv, mul_assoc]

end Factorization

section LocalFieldCancellation

variable [ValuativeRel k] [IsNonarchimedeanLocalField k] [Smooth G.X.hom]

local instance originalCorrectionsTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

include R in
/-- The two original epsilon corrections cancel on the entire actual common
Levi under the explicit root and algebraic character-detection inputs. -/
theorem originalCorrectionCharacter_product_eq_one
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    D.originalSourceCorrectionCharacter * D.originalTargetCorrectionCharacter = 1 := by
  let : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.rationalPoint_secondCountable k G
  rw [R.originalSourceCorrectionCharacter_eq_forward,
    R.originalTargetCorrectionCharacter_eq_forward]
  exact forwardCorrectionCharacter_product_eq_one (D := D) (R := R) hroot hinj

end LocalFieldCancellation

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
