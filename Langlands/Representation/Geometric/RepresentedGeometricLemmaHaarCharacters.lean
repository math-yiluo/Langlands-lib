import Langlands.Representation.Geometric.RepresentedGeometricLemmaIntersectionPoints
import Langlands.Representation.Geometric.RepresentedParabolicCoinvariants
import Langlands.Representation.Aubert.General.RationalGeometricEpsilonFactorization

/-! # Original Haar characters on a represented intersection Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance haarCharactersAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

/-- The positive half of the original radical's actual Haar character on the
represented Levi's own rational points. -/
def leviInducingHalfCharacter (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    Induction.SmoothCharacter ℂ (rationalPoints M) := by
  letI := leviPointTopology l hl
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let hn := pointImage_le_normalizer p l r hr
  let e := leviPointsEquiv p l hp hl
  exact {
    toMonoidHom := (HaarModulus.closedHalfCharacter
      (pointImage (r ≫ p)) hc (pointImage (l ≫ p)) hn).comp e.toMonoidHom
    isOpen_ker := (HaarModulus.isOpen_ker_closedHalfCharacter
      (pointImage (r ≫ p)) hc (pointImage (l ≫ p)) hn).preimage e.continuous }

variable
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

local notation "MI" => pointImage (lQ ≫ q)
local notation "MJ" => pointImage (l ≫ p)
local notation "UI" => pointImage (rQ ≫ q)
local notation "UJ" => pointImage (r ≫ p)
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ z⁻¹) MI
local notation "hUI" =>
  isClosed_pointImage_comp q rQ (hq.isClosedSubgroup)
    (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hUJ" =>
  isClosed_pointImage_comp p r (hp.isClosedSubgroup)
    (IsUnipotentRadical.isClosedSubgroup (And.left hr))
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ
local notation "hMJUJ" => pointImage_le_normalizer p l r hr

/-- The actual target intersection Levi, retaining its copy inside the
original target Levi image. -/
def targetCommonLeviPointsEquiv :
    letI := leviPointTopology D.lQ' D.hlQ'
    rationalPoints D.L' ≃ₜ* Lt := by
  letI := leviPointTopology D.lQ' D.hlQ'
  exact D.targetLeviPointsEquiv.trans
    (subgroupOfContinuousEquiv
      (inf_le_left : geometricTargetIntersection MI MJ z⁻¹ ≤ MI)).symm

@[simp]
theorem targetCommonLeviPointsEquiv_apply_coe (x : rationalPoints D.L') :
    ((D.targetCommonLeviPointsEquiv x : MI) : rationalPoints G) =
      rationalPoints.map (D.lQ' ≫ D.q' ≫ lQ ≫ q) x := rfl

/-- The source point of the generic Haar correction is exactly the actual
source-Levi inclusion following the supplied conjugation map `D.e`. -/
theorem sourceCorrectionTransport_commonLevi (x : rationalPoints D.L') :
    (geometricSourceCorrectionTransport MI MJ z⁻¹ (D.targetCommonLeviPointsEquiv x)).val =
      leviPointsEquiv p l hp hl
        (rationalPoints.map (D.l' ≫ D.p') (D.e x)) := by
  apply Subtype.ext
  change
    (geometricSourceCorrectionTransport MI MJ z⁻¹
      (D.targetCommonLeviPointsEquiv x)).val.val =
        rationalPoints.map (l ≫ p) (rationalPoints.map (D.l' ≫ D.p') (D.e x))
  rw [geometricSourceCorrectionTransport_apply,
    D.targetCommonLeviPointsEquiv_apply_coe, inv_inv]
  simpa only [pointMap_comp_apply] using (D.conjugationPoints_apply x).symm

/-- The original inducing half-character pulled through the actual `D.e`
is the positive half-modulus of the literal conjugate source radical. -/
theorem inducingHalfCharacter_commonLevi :
    letI := leviPointTopology l hl
    letI := leviPointTopology D.l' D.hl'
    letI := leviPointTopology D.lQ' D.hlQ'
    (leviInducingHalfCharacter p l r hp hr hl).toMonoidHom.comp
        ((rationalPoints.map (D.l' ≫ D.p')).comp D.e.toMonoidHom) =
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
        (geometricForwardSourceRadicalModulus MI MJ z⁻¹ UJ hUJ hMJUJ))).comp
          D.targetCommonLeviPointsEquiv.toMonoidHom := by
  letI := leviPointTopology l hl
  letI := leviPointTopology D.l' D.hl'
  letI := leviPointTopology D.lQ' D.hlQ'
  rw [← geometricSourceCorrectionRadicalModulus_eq_forward]
  apply MonoidHom.ext
  intro x
  change HaarModulus.closedHalfCharacter UJ hUJ MJ hMJUJ
      (leviPointsEquiv p l hp hl
        (rationalPoints.map (D.l' ≫ D.p') (D.e x))) =
    HaarModulus.closedHalfCharacter UJ hUJ MJ hMJUJ
      (geometricSourceCorrectionTransport MI MJ z⁻¹
        (D.targetCommonLeviPointsEquiv x)).val
  rw [D.sourceCorrectionTransport_commonLevi]

/-- The original target Jacquet inverse half-character restricts to the
actual target-radical Haar character at the same target common-Levi point. -/
theorem targetInverseHalfCharacter_commonLevi :
    letI := leviPointTopology lQ hlQ
    letI := leviPointTopology D.lQ' D.hlQ'
    (leviInverseHalfCharacter q lQ rQ hq hrQ hlQ).toMonoidHom.comp
        (rationalPoints.map (D.lQ' ≫ D.q')) =
      (Jacquet.inverseHalfCharacter
        (geometricTargetCorrectionRadicalModulus MI MJ z⁻¹ UI hUI hMIUI)).comp
          D.targetCommonLeviPointsEquiv.toMonoidHom := by
  letI := leviPointTopology lQ hlQ
  letI := leviPointTopology D.lQ' D.hlQ'
  apply MonoidHom.ext
  intro x
  change HaarModulus.closedInverseHalfCharacter UI hUI MI hMIUI
      (leviPointsEquiv q lQ hq hlQ (rationalPoints.map (D.lQ' ≫ D.q') x)) =
    HaarModulus.closedInverseHalfCharacter UI hUI MI hMIUI
      (D.targetCommonLeviPointsEquiv x).val
  congr 1

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
