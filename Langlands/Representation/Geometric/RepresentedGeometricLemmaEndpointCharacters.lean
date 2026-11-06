import Langlands.Representation.Geometric.RepresentedGeometricLemmaHaarCharacters
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.Aubert.General.RationalGeometricNormalizedEndpointCharacter

/-! # Actual inner endpoint characters of a represented geometric-lemma datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance endpointCharactersAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
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

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- A subgroup of the represented Levi has exactly its composite ambient image
under the actual Levi point equivalence. -/
theorem mem_pointImage_leviPointsEquiv {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ M) (x : rationalPoints M) :
    x ∈ pointImage j ↔
      leviPointsEquiv p l hp hl x ∈
        (pointImage (j ≫ l ≫ p)).subgroupOf (pointImage (l ≫ p)) := by
  let := leviPointTopology l hl
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, pointMap_comp_apply j (l ≫ p) y⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (leviPointsEquiv p l hp hl).injective ?_⟩
    apply Subtype.ext
    exact (pointMap_comp_apply j (l ≫ p) y).symm.trans hy

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UI" => pointImage (rQ ≫ q)
local notation "UJ" => pointImage (r ≫ p)
local notation "Ls" => Subgroup.subgroupOf (geometricSourceIntersection MI MJ z⁻¹) MJ
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ z⁻¹) MI
local notation "hMI" => isClosed_leviPoints q lQ hq hlQ
local notation "hMJ" => isClosed_leviPoints p l hp hl
local notation "hUI" => isClosed_pointImage_comp q rQ (hq.isClosedSubgroup)
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hUJ" => isClosed_pointImage_comp p r (hp.isClosedSubgroup)
  (IsUnipotentRadical.isClosedSubgroup (And.left hr))
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ
local notation "hMJUJ" => pointImage_le_normalizer p l r hr

/-- The actual source common Levi with its retained copy in the source Levi. -/
def sourceCommonLeviPointsEquiv :
    letI := leviPointTopology D.l' D.hl'
    rationalPoints D.M' ≃ₜ* Ls := by
  letI := leviPointTopology D.l' D.hl'
  have heq : pointImage (l ≫ p) ⊓
      (pointImage (lQ ≫ q)).map (MulAut.conj z).toMonoidHom =
      geometricSourceIntersection MI MJ z⁻¹ := by
    simp only [geometricSourceIntersection, inv_inv]
    rfl
  exact D.sourceLeviPointsEquiv.trans ((subgroupCongrContinuous heq).trans
    (subgroupOfContinuousEquiv
      (inf_le_left : geometricSourceIntersection MI MJ z⁻¹ ≤ MJ)).symm)

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem sourceCommonLeviPointsEquiv_apply_coe (x : rationalPoints D.M') :
    ((D.sourceCommonLeviPointsEquiv x : MJ) : rationalPoints G) =
      rationalPoints.map (D.l' ≫ D.p' ≫ l ≫ p) x := rfl

/-- The generic common-Levi conjugation is the supplied actual map `D.e`. -/
theorem intersectionSubgroupEquiv_commonLevi (x : rationalPoints D.L') :
    geometricIntersectionSubgroupEquiv MI MJ z⁻¹ (D.targetCommonLeviPointsEquiv x) =
      D.sourceCommonLeviPointsEquiv (D.e x) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [geometricIntersectionSubgroupEquiv_apply,
    D.targetCommonLeviPointsEquiv_apply_coe,
    D.sourceCommonLeviPointsEquiv_apply_coe, inv_inv]
  exact (D.conjugationPoints_apply x).symm

include D in
omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Normalization of the literal source endpoint radical by the common Levi. -/
theorem sourceCommonLevi_normalizesRadical :
    Ls ≤ Subgroup.normalizer
      ((geometricSourceIntersection UI MJ z⁻¹).subgroupOf MJ) := by
  apply normalizes_subgroupOf
  simpa only [geometricSourceIntersection, inv_inv, MulEquiv.toMonoidHom_eq_coe] using
    (D.sourcePoints_isSemidirectDecomposition).levi_le_normalizer

include D in
omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Normalization of the literal target endpoint radical by the common Levi. -/
theorem targetCommonLevi_normalizesRadical :
    Lt ≤ Subgroup.normalizer
      ((geometricTargetIntersection MI UJ z⁻¹).subgroupOf MI) :=
  normalizes_subgroupOf (D.targetPoints_isSemidirectDecomposition).levi_le_normalizer

/-- The actual inner source Jacquet inverse half is the literal endpoint
inverse half, retaining the original source ambient Levi. -/
theorem sourceInverseHalfCharacter_endpoint :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    (leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom =
      (geometricSourceEndpointInverseHalfCharacter MI MJ UI z⁻¹ hUI hMJ
        D.sourceCommonLevi_normalizesRadical).comp
          D.sourceCommonLeviPointsEquiv.toMonoidHom := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  let := (hMJ).locallyCompactSpace
  have hS (x : rationalPoints M) :
      x ∈ pointImage (D.r' ≫ D.p') ↔
        leviPointsEquiv p l hp hl x ∈
          (geometricSourceIntersection UI MJ z⁻¹).subgroupOf MJ := by
    have heq : pointImage ((D.r' ≫ D.p') ≫ l ≫ p) =
        geometricSourceIntersection UI MJ z⁻¹ := by
      simpa only [Category.assoc, geometricSourceIntersection, inv_inv,
        MulEquiv.toMonoidHom_eq_coe] using
        D.sourceRadicalPoints_eq
    rw [← heq]
    exact mem_pointImage_leviPointsEquiv (D.r' ≫ D.p') x
  have hL (x : rationalPoints M) :
      x ∈ pointImage (D.l' ≫ D.p') ↔
        leviPointsEquiv p l hp hl x ∈ Ls := by
    have heq : pointImage ((D.l' ≫ D.p') ≫ l ≫ p) =
        geometricSourceIntersection MI MJ z⁻¹ := by
      simpa only [Category.assoc, geometricSourceIntersection, inv_inv,
        MulEquiv.toMonoidHom_eq_coe] using
        D.sourceLeviPoints_eq
    rw [← heq]
    exact mem_pointImage_leviPointsEquiv (D.l' ≫ D.p') x
  apply MonoidHom.ext
  intro x
  change HaarModulus.closedInverseHalfCharacter
      (pointImage (D.r' ≫ D.p')) _ (pointImage (D.l' ≫ D.p')) _
      (leviPointsEquiv D.p' D.l' D.hp' D.hl' x) = _
  rw [GroupTransport.closedInverseHalfCharacter_transport
    (leviPointsEquiv p l hp hl) hS hL
    ((isClosed_geometricSourceIntersection UI MJ hUI hMJ z⁻¹).preimage
      continuous_subtype_val)
    (isClosed_pointImage_comp D.p' D.r' D.hp'.isClosedSubgroup D.hr'.1.isClosedSubgroup)
    D.sourceCommonLevi_normalizesRadical
    (pointImage_le_normalizer D.p' D.l' D.r' D.hr')]
  change _ = HaarModulus.closedInverseHalfCharacter
    ((geometricSourceIntersection UI MJ z⁻¹).subgroupOf MJ)
    ((isClosed_geometricSourceIntersection UI MJ hUI hMJ z⁻¹).preimage
      continuous_subtype_val)
    Ls D.sourceCommonLevi_normalizesRadical (D.sourceCommonLeviPointsEquiv x)
  congr 1

/-- The original inner source inverse half, transported through the actual
`D.e`, is the inverse half of the forward source-endpoint modulus. -/
theorem sourceInverseHalfCharacter_commonLevi :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    letI := leviPointTopology D.lQ' D.hlQ'
    (leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom.comp
        D.e.toMonoidHom =
      (Jacquet.inverseHalfCharacter
        (geometricCommonLeviIntersectionModulus MI MJ z⁻¹ UI MJ hUI hMJ
          hMIUI (fun _ hx => Subgroup.le_normalizer hx))).comp
        D.targetCommonLeviPointsEquiv.toMonoidHom := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  rw [D.sourceInverseHalfCharacter_endpoint]
  apply MonoidHom.ext
  intro x
  change geometricSourceEndpointInverseHalfCharacter MI MJ UI z⁻¹ hUI hMJ
      D.sourceCommonLevi_normalizesRadical (D.sourceCommonLeviPointsEquiv (D.e x)) = _
  rw [← D.intersectionSubgroupEquiv_commonLevi]
  exact congrArg (fun χ => χ (D.targetCommonLeviPointsEquiv x))
    (geometricSourceEndpointInverseHalfCharacter_transport MI MJ UI z⁻¹ hUI hMJ
      hMIUI D.sourceCommonLevi_normalizesRadical)

/-- The actual inner target induction half is the literal endpoint half,
retaining the original target ambient Levi. -/
theorem targetHalfCharacter_endpoint :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    letI := leviPointTopology D.lQ' D.hlQ'
    (leviInducingHalfCharacter D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ').toMonoidHom =
      (geometricTargetEndpointHalfCharacter MI MJ UJ z⁻¹ hMI hUJ
        D.targetCommonLevi_normalizesRadical).comp
          D.targetCommonLeviPointsEquiv.toMonoidHom := by
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.lQ' D.hlQ'
  let := (hMI).locallyCompactSpace
  have hS (x : rationalPoints L) :
      x ∈ pointImage (D.rQ' ≫ D.q') ↔
        leviPointsEquiv q lQ hq hlQ x ∈
          (geometricTargetIntersection MI UJ z⁻¹).subgroupOf MI := by
    have heq : pointImage ((D.rQ' ≫ D.q') ≫ lQ ≫ q) =
        geometricTargetIntersection MI UJ z⁻¹ := by
      simpa only [Category.assoc, geometricTargetIntersection,
        MulEquiv.toMonoidHom_eq_coe] using D.targetRadicalPoints_eq
    rw [← heq]
    exact mem_pointImage_leviPointsEquiv (D.rQ' ≫ D.q') x
  have hL (x : rationalPoints L) :
      x ∈ pointImage (D.lQ' ≫ D.q') ↔
        leviPointsEquiv q lQ hq hlQ x ∈ Lt := by
    have heq : pointImage ((D.lQ' ≫ D.q') ≫ lQ ≫ q) =
        geometricTargetIntersection MI MJ z⁻¹ := by
      simpa only [Category.assoc, geometricTargetIntersection,
        MulEquiv.toMonoidHom_eq_coe] using D.targetLeviPoints_eq
    rw [← heq]
    exact mem_pointImage_leviPointsEquiv (D.lQ' ≫ D.q') x
  apply MonoidHom.ext
  intro x
  change HaarModulus.closedHalfCharacter
      (pointImage (D.rQ' ≫ D.q')) _ (pointImage (D.lQ' ≫ D.q')) _
      (leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ' x) = _
  rw [GroupTransport.closedHalfCharacter_transport
    (leviPointsEquiv q lQ hq hlQ) hS hL
    ((isClosed_geometricTargetIntersection MI UJ hMI hUJ z⁻¹).preimage
      continuous_subtype_val)
    (isClosed_pointImage_comp D.q' D.rQ' D.hq'.isClosedSubgroup D.hrQ'.1.isClosedSubgroup)
    D.targetCommonLevi_normalizesRadical
    (pointImage_le_normalizer D.q' D.lQ' D.rQ' D.hrQ')]
  change _ = HaarModulus.closedHalfCharacter
    ((geometricTargetIntersection MI UJ z⁻¹).subgroupOf MI)
    ((isClosed_geometricTargetIntersection MI UJ hMI hUJ z⁻¹).preimage
      continuous_subtype_val)
    Lt D.targetCommonLevi_normalizesRadical (D.targetCommonLeviPointsEquiv x)
  congr 1

/-- The original inner target induction half is the positive half of the
literal target-endpoint intersection modulus on the entire common Levi. -/
theorem targetHalfCharacter_commonLevi :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    letI := leviPointTopology D.lQ' D.hlQ'
    (leviInducingHalfCharacter D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ').toMonoidHom =
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
        (geometricCommonLeviIntersectionModulus MI MJ z⁻¹ MI UJ hMI hUJ
          (fun _ hx => Subgroup.le_normalizer hx) hMJUJ))).comp
        D.targetCommonLeviPointsEquiv.toMonoidHom := by
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.lQ' D.hlQ'
  rw [D.targetHalfCharacter_endpoint,
    geometricTargetEndpointHalfCharacter_eq MI MJ UJ z⁻¹ hMI hUJ hMJUJ
      D.targetCommonLevi_normalizesRadical]

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
