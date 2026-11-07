import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactCoefficient
import Langlands.Representation.Geometric.RepresentedGeometricLemmaNormalizedCoefficient
import Langlands.Representation.Induction.CharacterTwistProof

/-! # The original normalized coefficient of the represented compact integral -/

noncomputable section

universe u v

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactNormalizationAmbientTopology :
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

local instance compactNormalizationCommonLeviTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "MI" => pointImage (lQ ≫ q)
local notation "UI" => pointImage (rQ ≫ q)
local notation "Kt" => geometricTargetIntersection MI (pointImage p) z⁻¹
local notation "hUI" => isClosed_pointImage_comp q rQ hq.isClosedSubgroup
  (IsUnipotentRadical.isClosedSubgroup (And.left hrQ))
local notation "hMIUI" => pointImage_le_normalizer q lQ rQ hrQ

/-- The original target inverse-half character, on its original Levi image. -/
def compactOuterInverseHalfAmbient
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) : SmoothCharacter ℂ MI where
  toMonoidHom := HaarModulus.closedInverseHalfCharacter UI hUI MI hMIUI
  isOpen_ker := HaarModulus.isOpen_ker_closedInverseHalfCharacter UI hUI MI hMIUI

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Pullback to the original target Levi's own points gives exactly the
inverse half in its original normalized Jacquet functor. -/
theorem compactOuterInverseHalfAmbient_eq_original :
    letI := leviPointTopology lQ hlQ
    D.compactOuterInverseHalfAmbient.toMonoidHom.comp
        (leviPointsEquiv q lQ hq hlQ).toMonoidHom =
      (leviInverseHalfCharacter q lQ rQ hq hrQ hlQ).toMonoidHom := rfl

/-- Restriction of the original target normalization to the full target
intersection, without replacing it by a common-Levi value. -/
def compactOuterInverseHalfCharacter : Kt →* ℂˣ :=
  D.compactOuterInverseHalfAmbient.toMonoidHom.comp (Subgroup.inclusion inf_le_left)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem compactOuterInverseHalfCharacter_eq :
    D.compactOuterInverseHalfCharacter =
      Jacquet.inverseHalfCharacter D.targetIntersectionRadicalModulus := rfl

/-- The scalar product actually supplied by outer normalization, the
relative compact integral and the original source inducing half. -/
def compactNormalizedCoefficientCharacter : Kt →* ℂˣ :=
  D.compactOuterInverseHalfCharacter * D.compactIntegralHaarCharacter *
    D.compactSourceHalfCharacter

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The full source inducing half is the actual source-radical half after
the original target common-Levi projection. -/
theorem compactSourceHalfCharacter_eq_forward :
    D.compactSourceHalfCharacter =
      (Jacquet.complexCharacter
        (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus)).comp
          D.targetIntersectionLeviProjection := by
  let := leviPointTopology l hl
  let := leviPointTopology D.l' D.hl'
  apply MonoidHom.ext
  intro x
  exact congrArg (fun f : rationalPoints D.L' →* ℂˣ =>
    f (D.compactTargetLeviProjection x)) D.inducingHalfCharacter_commonLevi

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The complete actual compact-integral scalar is the published normalized
coefficient on the whole literal target intersection. -/
theorem compactNormalizedCoefficientCharacter_eq :
    D.compactNormalizedCoefficientCharacter =
      D.normalizedTargetIntersectionCoefficientCharacter := by
  apply MonoidHom.ext
  intro x
  have hsquare :
      Jacquet.complexCharacter
          (Jacquet.positiveHalfCharacter D.targetIntersectionRadicalModulus) x ^ 2 =
        Jacquet.complexCharacter D.targetIntersectionRadicalModulus x := by
    simpa only [Jacquet.complexCharacter, MonoidHom.comp_apply, map_pow] using
      congrArg (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        (Jacquet.positiveHalfCharacter_sq D.targetIntersectionRadicalModulus x)
  simp only [compactNormalizedCoefficientCharacter, MonoidHom.mul_apply,
    D.compactOuterInverseHalfCharacter_eq, D.compactIntegralHaarCharacter_eq_ambient,
    D.compactSourceHalfCharacter_eq_forward, MonoidHom.comp_apply]
  change (Jacquet.complexCharacter
      (Jacquet.positiveHalfCharacter D.targetIntersectionRadicalModulus) x)⁻¹ *
    (Jacquet.complexCharacter D.targetIntersectionRadicalModulus x /
      Jacquet.complexCharacter D.targetIntersectionCorrectionModulus x) *
    Jacquet.complexCharacter (Jacquet.positiveHalfCharacter D.forwardSourceRadicalModulus)
      (D.targetIntersectionLeviProjection x) = _
  rw [← hsquare, pow_two]
  simp only [normalizedTargetIntersectionCoefficientCharacter, MonoidHom.mul_apply,
    MonoidHom.div_apply, MonoidHom.comp_apply, div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel, one_mul]

variable (A : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The three actual scalar twists give exactly the published normalized
coefficient representation on the original source quotient. -/
theorem compactNormalizedSourceAction_eq :
    letI := leviPointTopology l hl
    Langlands.twist D.compactOuterInverseHalfCharacter
        (Langlands.twist D.compactIntegralHaarCharacter (D.compactSourceQuotientAction A)) =
      D.normalizedTargetIntersectionCoefficientAction A := by
  let := leviPointTopology l hl
  unfold compactSourceQuotientAction
  rw [Langlands.twist_twist, Langlands.twist_twist]
  change Langlands.twist D.compactNormalizedCoefficientCharacter _ = _
  rw [D.compactNormalizedCoefficientCharacter_eq]
  rfl

namespace DynamicRealization

variable {D} (R : D.DynamicRealization)

/-- The actual nested compact-integral coefficient, with the original outer
target inverse half, is the normalized full-target source coefficient. -/
def compactNormalizedCoefficientEquiv :
    letI := leviPointTopology l hl
    (Langlands.twist D.compactOuterInverseHalfCharacter
      (Langlands.twist D.compactIntegralHaarCharacter
        (R.compactNestedCoefficientAction A))).Equiv
      (D.normalizedTargetIntersectionCoefficientAction A) := by
  letI := leviPointTopology l hl
  let E := Langlands.twistEquiv D.compactOuterInverseHalfCharacter
    (R.compactIntegralCoefficientSourceEquiv A)
  refine { toLinearEquiv := E.toLinearEquiv, isIntertwining' := ?_ }
  intro x
  have hact :
      (Langlands.twist D.compactOuterInverseHalfCharacter
        (Langlands.twist D.compactIntegralHaarCharacter
          (D.compactSourceQuotientAction A))) x =
        (D.normalizedTargetIntersectionCoefficientAction A) x :=
    congrArg (fun ρ : Representation ℂ Kt
      (Jacquet.Localization.Coinvariants A.representation (pointImage (D.r' ≫ D.p')) 1) =>
        ρ x) (D.compactNormalizedSourceAction_eq A)
  exact (E.isIntertwining' x).trans
    (congrArg (fun f => f.comp E.toLinearEquiv.toLinearMap) hact)

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "sQ" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "S" => compactComparisonSaturation D
local notation "hker" => projectionKernel_le_compactComparisonSaturation D
local notation "rS" => splitStagesRetraction π sQ
  (fun m => IsSemidirectDecomposition.projection_levi dQ m) S hker
local notation "HS" => Subgroup.subgroupOf H S
local notation "j" => MonoidHom.subgroupComap (Subgroup.subtype (MonoidHom.ker rS)) HS
local notation "φ" => MulEquiv.toMonoidHom
  (Subgroup.subgroupOfEquivOfLe (stabilizer_le_compactComparisonSaturation R))
local notation "σ" => Rep.ρ
  (Functor.obj (stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z) A)
local notation "Rs" => pointImage (D.r' ≫ D.p')

@[simp] theorem compactNormalizedCoefficientEquiv_mk (a : A) :
    letI := leviPointTopology l hl
    R.compactNormalizedCoefficientEquiv A
      (Representation.Coinvariants.mk (((σ).comp φ).comp j) a) =
        Jacquet.Localization.mk A.representation Rs 1 a := rfl

/-- Every original source intertwiner commutes with the normalized coefficient
comparison and its actual source Jacquet quotient map. -/
theorem compactNormalizedCoefficientEquiv_natural
    {B : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M)}
    (T : A ⟶ B)
    (x : letI := leviPointTopology l hl;
      Representation.Coinvariants (((σ).comp φ).comp j)) :
    letI := leviPointTopology l hl
    R.compactNormalizedCoefficientEquiv B
        (Langlands.twistIntertwining D.compactOuterInverseHalfCharacter
          (Langlands.twistIntertwining D.compactIntegralHaarCharacter
            (R.compactNestedCoefficientMap T)) x) =
      Jacquet.Localization.mapLinear Rs 1 (SmoothRep.hom T)
        (R.compactNormalizedCoefficientEquiv A x) := by
  let := leviPointTopology l hl
  exact R.compactIntegralCoefficientSourceEquiv_natural T x

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
