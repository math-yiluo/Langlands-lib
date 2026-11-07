import Langlands.Representation.Geometric.RepresentedGeometricLemmaRawQuotient
import Langlands.Representation.Geometric.RepresentedGeometricLemmaCoefficient

/-! # The actual common-Levi action on the coefficient quotient -/

noncomputable section

universe u v

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance quotientActionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
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

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (IsSemidirectDecomposition.projection dQ))
local notation "fH" => stabilizerToLeviPoints p l r hp hr hl hmul q z
local notation "R" => pointImage (D.r' ≫ D.p')
local notation "χ" => leviInducingHalfCharacter p l r hp hr hl

/-- The original target common Levi maps into the full stabilizer by its
literal ambient inclusion. -/
def commonLeviToStabilizer : rationalPoints D.L' →* H := by
  letI := leviPointTopology D.lQ' D.hlQ'
  exact D.targetParabolicPointsToStabilizer.comp
    ((Subgroup.inclusion D.targetPoints_isSemidirectDecomposition.levi_le).comp
      D.targetLeviPointsEquiv.toMonoidHom)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem commonLeviToStabilizer_apply_coe (x : rationalPoints D.L') :
    ((D.commonLeviToStabilizer x : pointImage q) : rationalPoints G) =
      rationalPoints.map (D.lQ' ≫ D.q' ≫ lQ ≫ q) x := rfl

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The original source Levi projection recovers the supplied conjugation
map on the actual common Levi. -/
theorem stabilizerToLeviPoints_commonLeviToStabilizer (x : rationalPoints D.L') :
    letI := leviPointTopology l hl
    fH (D.commonLeviToStabilizer x) =
      rationalPoints.map (D.l' ≫ D.p') (D.e x) := by
  let _ := leviPointTopology l hl
  let dP := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hsource :
      Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹
        (D.commonLeviToStabilizer x) =
      Subgroup.inclusion dP.levi_le
        (leviPointsEquiv p l hp hl (rationalPoints.map (D.l' ≫ D.p') (D.e x))) := by
    apply Subtype.ext
    rw [Geometric.stabilizerToInducing_apply, D.commonLeviToStabilizer_apply_coe,
      inv_inv, ← D.conjugationPoints_apply]
    simp only [pointMap_comp_apply]
    rfl
  change (leviPointsEquiv p l hp hl).symm (dP.projection
    (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹
      (D.commonLeviToStabilizer x))) = _
  rw [hsource]
  change (leviPointsEquiv p l hp hl).symm
    (dP.projection ⟨leviPointsEquiv p l hp hl
      (rationalPoints.map (D.l' ≫ D.p') (D.e x)), _⟩) = _
  rw [dP.projection_levi, ContinuousMulEquiv.symm_apply_apply]

/-- The correction needed to express the raw coefficient quotient through
the original normalized source-intersection Jacquet module. -/
def sourceQuotientCorrectionCharacter : rationalPoints D.L' →* ℂˣ := by
  letI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPoints_locallyCompactSpace p l hp hl
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  letI := leviPointTopology D.l' D.hl'
  exact ((χ).toMonoidHom.comp (rationalPoints.map (D.l' ≫ D.p'))).comp
      D.e.toMonoidHom *
    ((leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom.comp
      D.e.toMonoidHom)⁻¹

/-- The actual common-Levi action on full-stabilizer kernel coinvariants. -/
def stabilizerCommonLeviQuotientAction
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    Representation ℂ (rationalPoints D.L')
      (Jacquet.Coinvariants
        ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH) := by
  letI := leviPointTopology l hl
  letI : (NQH).Normal := inferInstance
  exact (Representation.toCoinvariants
    ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH).comp
      D.commonLeviToStabilizer

/-- Under the explicit reverse image inclusion, the original raw quotient
action is the correction twist of the actual normalized source Jacquet
module transported through the supplied original map D.e. -/
def stabilizerCommonLeviSourceJacquetEquiv
    (himage : Subgroup.map fH NQH ≤ R)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    (D.stabilizerCommonLeviQuotientAction A).Equiv
      (Langlands.twist D.sourceQuotientCorrectionCharacter
        (((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj A).representation.comp
          D.e.toMonoidHom)) := by
  letI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPoints_locallyCompactSpace p l hp hl
  letI := leviPoints_nonarchimedeanGroup p l hp hl
  letI := leviPointTopology D.l' D.hl'
  refine {
    toLinearEquiv := D.stabilizerCoinvariantsSourceEquiv himage A
    isIntertwining' := ?_ }
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := Jacquet.mk_surjective
    ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH y
  change A at a
  change D.stabilizerCoinvariantsSourceEquiv himage A
    (Jacquet.mk _ NQH
      (((χ).toMonoidHom (fH (D.commonLeviToStabilizer x)) : ℂ) •
        A.representation (fH (D.commonLeviToStabilizer x)) a)) = _
  simp only [D.stabilizerToLeviPoints_commonLeviToStabilizer,
    D.stabilizerCoinvariantsSourceEquiv_mk, map_smul]
  change _ =
    ((D.sourceQuotientCorrectionCharacter x : ℂˣ) : ℂ) •
      (((leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom
        (D.e x) : ℂ) •
        Jacquet.Localization.mk A.representation R 1
          (A.representation (rationalPoints.map (D.l' ≫ D.p') (D.e x)) a))
  simp only [sourceQuotientCorrectionCharacter, MonoidHom.mul_apply,
    MonoidHom.inv_apply, MonoidHom.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    smul_smul, mul_assoc]
  change _ =
    (((χ).toMonoidHom (rationalPoints.map (D.l' ≫ D.p') (D.e x)) : ℂ) *
      (((leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom
          (D.e x) : ℂ)⁻¹ *
        ((leviInverseHalfCharacter D.p' D.l' D.r' D.hp' D.hr' D.hl').toMonoidHom
          (D.e x) : ℂ))) • _
  rw [inv_mul_cancel₀ (Units.ne_zero _), mul_one]

@[simp]
theorem stabilizerCommonLeviSourceJacquetEquiv_mk
    (himage : Subgroup.map fH NQH ≤ R)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (a : A) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    D.stabilizerCommonLeviSourceJacquetEquiv himage A
        (Jacquet.mk
          ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH a) =
      Jacquet.Localization.mk A.representation R 1 a := rfl

/-- Every original coefficient morphism commutes with the common-Levi
representation equivalence. -/
theorem stabilizerCommonLeviSourceJacquetEquiv_natural
    (himage : Subgroup.map fH NQH ≤ R)
    {A B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (T : A ⟶ B)
    (x : letI := leviPointTopology l hl
      Jacquet.Coinvariants
        ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    D.stabilizerCommonLeviSourceJacquetEquiv himage B
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap
            (((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).map T).hom)
            NQH) x) =
      SmoothRep.hom ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').map T)
        (D.stabilizerCommonLeviSourceJacquetEquiv himage A x) := by
  let := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPoints_locallyCompactSpace p l hp hl
  let := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  exact D.stabilizerCoinvariantsSourceEquiv_natural himage T x

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
