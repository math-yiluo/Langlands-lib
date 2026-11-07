import Langlands.Representation.Geometric.RepresentedGeometricLemmaHaarModels
import Langlands.Representation.Geometric.RepresentedGeometricLemmaHaarCharacters

/-! # Forward Haar factors on the original represented common Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private theorem closedNormalizerCharacter_same_point
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {A B : Subgroup H}
    (hAB : A = B) (hA : IsClosed (A : Set H)) (hB : IsClosed (B : Set H))
    (a : Subgroup.normalizer (A : Set H)) (b : Subgroup.normalizer (B : Set H))
    (hab : (a : H) = (b : H)) :
    HaarModulus.closedNormalizerCharacter A hA a =
      HaarModulus.closedNormalizerCharacter B hB b := by
  subst B
  congr 1
  exact Subtype.ext hab

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance haarBalanceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

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

local instance haarBalanceCommonLeviPointTopology : TopologicalSpace (rationalPoints D.L') :=
  leviPointTopology D.lQ' D.hlQ'

local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UI" => pointImage (rQ ≫ q)
local notation "UJ" => pointImage (r ≫ p)
local notation "hMI" => isClosed_leviPoints q lQ hq hlQ
local notation "hMJ" => isClosed_leviPoints p l hp hl
local notation "hUI" => isClosed_pointImage_comp q rQ hq.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hUJ" => isClosed_pointImage_comp p r hp.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hr))
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ
local notation "hMJUJ" => pointImage_le_normalizer p l r hr
local notation "eL" => D.targetCommonLeviPointsEquiv.toMonoidHom
local notation "iZ" => D.lQ' ≫ D.q' ≫ lQ ≫ q
local notation "iT" => D.targetCommonTorusHom ≫ iZ

/-- The original target radical modulus on the original common Levi. -/
def forwardTargetRadicalModulus : rationalPoints D.L' →* ℝ≥0ˣ :=
  (geometricTargetCorrectionRadicalModulus MI MJ z⁻¹ UI hUI hMIUI).comp eL

/-- The inverse-conjugated original source radical modulus at the same point. -/
def forwardSourceRadicalModulus : rationalPoints D.L' →* ℝ≥0ˣ :=
  (geometricForwardSourceRadicalModulus MI MJ z⁻¹ UJ hUJ hMJUJ).comp eL

/-- The original source endpoint radical after inverse conjugation. -/
def forwardSourceEndpointModulus : rationalPoints D.L' →* ℝ≥0ˣ :=
  (geometricCommonLeviIntersectionModulus MI MJ z⁻¹ UI MJ hUI hMJ hMIUI
    (fun _ hx => Subgroup.le_normalizer hx)).comp eL

/-- The distinct original target endpoint radical modulus. -/
def forwardTargetEndpointModulus : rationalPoints D.L' →* ℝ≥0ˣ :=
  (geometricCommonLeviIntersectionModulus MI MJ z⁻¹ MI UJ hMI hUJ
    (fun _ hx => Subgroup.le_normalizer hx) hMJUJ).comp eL

/-- The modulus of the literal intersection of both original radicals. -/
def forwardIntersectionModulus : rationalPoints D.L' →* ℝ≥0ˣ :=
  (geometricCommonLeviIntersectionModulus MI MJ z⁻¹ UI UJ hUI hUJ hMIUI hMJUJ).comp eL

/-- The factorized source correction on the original common Levi. -/
def forwardSourceCorrectionCharacter : rationalPoints D.L' →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus) *
    Jacquet.inverseHalfCharacter D.forwardTargetEndpointModulus *
    Jacquet.inverseHalfCharacter D.forwardIntersectionModulus

/-- The factorized target correction on the original common Levi. -/
def forwardTargetCorrectionCharacter : rationalPoints D.L' →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardTargetRadicalModulus) *
    Jacquet.inverseHalfCharacter D.forwardSourceEndpointModulus *
    Jacquet.inverseHalfCharacter D.forwardIntersectionModulus

namespace DynamicRealization

variable (R : D.DynamicRealization)

local notation "chi" => CommGroupScheme.groupHom R.targetCocharacter ≫ iT
local notation "psi" => CommGroupScheme.groupHom R.sourceCocharacter ≫ iT

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The first dynamic point subgroup is the original target radical image. -/
theorem haarTargetRadicalPoints_eq :
    (Dynamic.unipotent chi).rationalPoints = UI := by
  change (Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) = _
  rw [← R.targetRadical, ← pointImage_eq_range_carrier]

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The second dynamic point subgroup is the original source radical conjugate. -/
theorem haarSourceRadicalPoints_eq :
    (Dynamic.unipotent psi).rationalPoints =
      (UJ).map (MulAut.conj z⁻¹).toMonoidHom := by
  change (Dynamic.unipotent psi).carrier (Over.mk (𝟙 _)) = _
  rw [← R.sourceRadical, ← pointImage_eq_range_carrier]
  exact rationalPoints_range_comp_innerIso (r ≫ p) z⁻¹

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The first axis is the forward image of the original source endpoint. -/
theorem haarSourceEndpointPoints_eq :
    (Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).rationalPoints =
      geometricTargetIntersection UI MJ z⁻¹ := by
  change (Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) ⊓
    (Dynamic.centralizer psi).carrier (Over.mk (𝟙 _)) = _
  rw [← R.targetRadical, ← R.sourceLevi,
    ← pointImage_eq_range_carrier, ← pointImage_eq_range_carrier]
  change UI ⊓ (rationalPoints.map ((l ≫ p) ≫ (G.innerIso z⁻¹).hom)).range = _
  rw [rationalPoints_range_comp_innerIso]
  rfl

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The other axis is the distinct original target endpoint. -/
theorem haarTargetEndpointPoints_eq :
    (Dynamic.unipotent psi ⊓ Dynamic.centralizer chi).rationalPoints =
      geometricTargetIntersection MI UJ z⁻¹ := by
  change (Dynamic.unipotent psi).carrier (Over.mk (𝟙 _)) ⊓
    (Dynamic.centralizer chi).carrier (Over.mk (𝟙 _)) = _
  rw [← R.sourceRadical, ← R.targetLevi,
    ← pointImage_eq_range_carrier, ← pointImage_eq_range_carrier]
  change (rationalPoints.map ((r ≫ p) ≫ (G.innerIso z⁻¹).hom)).range ⊓ MI = _
  rw [rationalPoints_range_comp_innerIso]
  exact inf_comm ((UJ).map (MulAut.conj z⁻¹).toMonoidHom) MI

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The common dynamic radical is the literal forward radical intersection. -/
theorem haarIntersectionPoints_eq :
    (Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).rationalPoints =
      geometricTargetIntersection UI UJ z⁻¹ := by
  change (Dynamic.unipotent chi).rationalPoints ⊓
    (Dynamic.unipotent psi).rationalPoints = _
  rw [R.haarTargetRadicalPoints_eq, R.haarSourceRadicalPoints_eq]
  rfl

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
theorem isClosed_haarTargetRadical :
    IsClosed ((Dynamic.unipotent chi).rationalPoints : Set (rationalPoints G)) := by
  rw [R.haarTargetRadicalPoints_eq]
  exact hUI

omit [LocallyCompactSpace (rationalPoints G)] in
theorem isClosed_haarSourceRadical :
    IsClosed ((Dynamic.unipotent psi).rationalPoints : Set (rationalPoints G)) := by
  rw [R.haarSourceRadicalPoints_eq]
  exact isClosed_map_conj UJ hUJ z⁻¹

omit [LocallyCompactSpace (rationalPoints G)] in
theorem isClosed_haarSourceEndpoint :
    IsClosed ((Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).rationalPoints :
      Set (rationalPoints G)) := by
  rw [R.haarSourceEndpointPoints_eq]
  exact isClosed_geometricTargetIntersection UI MJ hUI hMJ z⁻¹

omit [LocallyCompactSpace (rationalPoints G)] in
theorem isClosed_haarTargetEndpoint :
    IsClosed ((Dynamic.unipotent psi ⊓ Dynamic.centralizer chi).rationalPoints :
      Set (rationalPoints G)) := by
  rw [R.haarTargetEndpointPoints_eq]
  exact isClosed_geometricTargetIntersection MI UJ hMI hUJ z⁻¹

omit [LocallyCompactSpace (rationalPoints G)] in
theorem isClosed_haarIntersection :
    IsClosed ((Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).rationalPoints :
      Set (rationalPoints G)) := by
  rw [R.haarIntersectionPoints_eq]
  exact isClosed_geometricTargetIntersection UI UJ hUI hUJ z⁻¹

/-- The first dynamic Haar character is the literal target-radical modulus
at the original common-Levi point. -/
theorem haarTargetRadicalCharacter_eq_forward :
    RationalPointFamily.centralizingUnipotentHaarCharacter chi iZ
        R.haarCommonLevi_centralizes_target R.isClosed_haarTargetRadical =
      D.forwardTargetRadicalModulus := by
  apply MonoidHom.ext
  intro x
  exact closedNormalizerCharacter_same_point R.haarTargetRadicalPoints_eq
    R.isClosed_haarTargetRadical hUI _ _ rfl

/-- The second dynamic Haar character is the forward source-radical modulus. -/
theorem haarSourceRadicalCharacter_eq_forward :
    RationalPointFamily.centralizingUnipotentHaarCharacter psi iZ
        R.haarCommonLevi_centralizes_source R.isClosed_haarSourceRadical =
      D.forwardSourceRadicalModulus := by
  apply MonoidHom.ext
  intro x
  exact closedNormalizerCharacter_same_point R.haarSourceRadicalPoints_eq
    R.isClosed_haarSourceRadical (isClosed_map_conj UJ hUJ z⁻¹) _ _ rfl

/-- The first axis Haar character is the original source-endpoint modulus. -/
theorem haarSourceEndpointCharacter_eq_forward :
    RationalPointFamily.centralizingUnipotentCentralizerHaarCharacter chi psi iZ
        R.haarCommonLevi_centralizes_target R.haarCommonLevi_centralizes_source
        R.isClosed_haarSourceEndpoint =
      D.forwardSourceEndpointModulus := by
  apply MonoidHom.ext
  intro x
  exact closedNormalizerCharacter_same_point R.haarSourceEndpointPoints_eq
    R.isClosed_haarSourceEndpoint
    (isClosed_geometricTargetIntersection UI MJ hUI hMJ z⁻¹) _ _ rfl

/-- The distinct other axis Haar character is the original target endpoint. -/
theorem haarTargetEndpointCharacter_eq_forward :
    RationalPointFamily.centralizingUnipotentCentralizerHaarCharacter psi chi iZ
        R.haarCommonLevi_centralizes_source R.haarCommonLevi_centralizes_target
        R.isClosed_haarTargetEndpoint =
      D.forwardTargetEndpointModulus := by
  apply MonoidHom.ext
  intro x
  exact closedNormalizerCharacter_same_point R.haarTargetEndpointPoints_eq
    R.isClosed_haarTargetEndpoint
    (isClosed_geometricTargetIntersection MI UJ hMI hUJ z⁻¹) _ _ rfl

/-- The common dynamic Haar character is the literal radical-intersection
modulus at the same original acting point. -/
theorem haarIntersectionCharacter_eq_forward :
    RationalPointFamily.centralizingUnipotentIntersectionHaarCharacter chi psi iZ
        R.haarCommonLevi_centralizes_target R.haarCommonLevi_centralizes_source
        R.isClosed_haarIntersection =
      D.forwardIntersectionModulus := by
  apply MonoidHom.ext
  intro x
  exact closedNormalizerCharacter_same_point R.haarIntersectionPoints_eq
    R.isClosed_haarIntersection
    (isClosed_geometricTargetIntersection UI UJ hUI hUJ z⁻¹) _ _ rfl

section LocalFieldBalance

variable [ValuativeRel k] [IsNonarchimedeanLocalField k] [Smooth G.X.hom]

local instance haarBalanceAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance haarBalanceAmbientPointT2 : T2Space (rationalPoints G) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G

local instance haarBalanceTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

local instance haarBalanceSourceEndpointAffine : IsAffineHom D.N'.X.hom :=
  D.haarSourceEndpoint_closed.isAffineHom
local instance haarBalanceTargetEndpointAffine : IsAffineHom D.U'.X.hom :=
  D.haarTargetEndpoint_closed.isAffineHom
local instance haarBalanceIntersectionAffine : IsAffineHom D.haarIntersectionScheme.X.hom :=
  D.haarIntersection_closed.isAffineHom
local instance haarBalanceCommonLeviAffine : IsAffine D.L'.X.left := by
  let := D.haarCommonLevi_closed.isAffineHom
  exact isAffine_of_isAffineHom D.L'.X.hom

local instance haarBalanceSourceEndpointFiniteType : LocallyOfFiniteType D.N'.X.hom :=
  D.haarSourceEndpoint_closed.locallyOfFiniteType
local instance haarBalanceTargetEndpointFiniteType : LocallyOfFiniteType D.U'.X.hom :=
  D.haarTargetEndpoint_closed.locallyOfFiniteType
local instance haarBalanceIntersectionFiniteType :
    LocallyOfFiniteType D.haarIntersectionScheme.X.hom :=
  D.haarIntersection_closed.locallyOfFiniteType

include R

/-- The five literal forward Haar factors balance on every point of the
original common Levi under the explicit root and character-detection inputs. -/
theorem forwardHaarCharacter_product_square
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    D.forwardTargetRadicalModulus * D.forwardSourceRadicalModulus =
      D.forwardSourceEndpointModulus * D.forwardTargetEndpointModulus *
        D.forwardIntersectionModulus ^ 2 := by
  let : IsAffineHom U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).isAffineHom
  let : IsAffineHom N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).isAffineHom
  let : LocallyOfFiniteType U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).locallyOfFiniteType
  let : LocallyOfFiniteType N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).locallyOfFiniteType
  have hi := D.targetCommonTorus_isMaximalSplitTorus_ambient
  have h :=
    RationalPointFamily.centralizingHaarCharacter_product_square_of_characterRestrict_injective
      hroot hi.1.1 R.targetCocharacter R.sourceCocharacter iZ
      R.haarCommonLevi_centralizes_target R.haarCommonLevi_centralizes_source
      R.haarTargetRadical_represented R.haarSourceRadical_represented
      R.haarSourceEndpoint_represented R.haarTargetEndpoint_represented
      R.haarIntersection_represented D.targetCommonTorusHom rfl
      (Lie.finiteCoordinates U) (Lie.finiteCoordinates N)
      (Lie.finiteCoordinates D.N') (Lie.finiteCoordinates D.U')
      (Lie.finiteCoordinates D.haarIntersectionScheme)
      R.isClosed_haarTargetRadical R.isClosed_haarSourceRadical
      R.isClosed_haarSourceEndpoint R.isClosed_haarTargetEndpoint
      R.isClosed_haarIntersection hinj
  simpa only [R.haarTargetRadicalCharacter_eq_forward,
    R.haarSourceRadicalCharacter_eq_forward, R.haarSourceEndpointCharacter_eq_forward,
    R.haarTargetEndpointCharacter_eq_forward, R.haarIntersectionCharacter_eq_forward] using h

/-- The factorized correction characters are reciprocal on the entire
original target common Levi under those same explicit inputs. -/
theorem forwardCorrectionCharacter_product_eq_one
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    D.forwardSourceCorrectionCharacter * D.forwardTargetCorrectionCharacter = 1 := by
  let : IsAffineHom U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).isAffineHom
  let : IsAffineHom N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).isAffineHom
  let : LocallyOfFiniteType U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).locallyOfFiniteType
  let : LocallyOfFiniteType N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).locallyOfFiniteType
  have hi := D.targetCommonTorus_isMaximalSplitTorus_ambient
  have h :=
    RationalPointFamily.centralizingHaarCharacter_correctionProduct_eq_one_of_characterRestrict_injective
      hroot hi.1.1 R.targetCocharacter R.sourceCocharacter iZ
      R.haarCommonLevi_centralizes_target R.haarCommonLevi_centralizes_source
      R.haarTargetRadical_represented R.haarSourceRadical_represented
      R.haarSourceEndpoint_represented R.haarTargetEndpoint_represented
      R.haarIntersection_represented D.targetCommonTorusHom rfl
      (Lie.finiteCoordinates U) (Lie.finiteCoordinates N)
      (Lie.finiteCoordinates D.N') (Lie.finiteCoordinates D.U')
      (Lie.finiteCoordinates D.haarIntersectionScheme)
      R.isClosed_haarTargetRadical R.isClosed_haarSourceRadical
      R.isClosed_haarSourceEndpoint R.isClosed_haarTargetEndpoint
      R.isClosed_haarIntersection hinj
  simpa only [R.haarTargetRadicalCharacter_eq_forward,
    R.haarSourceRadicalCharacter_eq_forward, R.haarSourceEndpointCharacter_eq_forward,
    R.haarTargetEndpointCharacter_eq_forward, R.haarIntersectionCharacter_eq_forward,
    forwardSourceCorrectionCharacter, forwardTargetCorrectionCharacter] using h

end LocalFieldBalance

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
