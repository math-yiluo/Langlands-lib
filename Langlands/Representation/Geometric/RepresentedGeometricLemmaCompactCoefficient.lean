import Langlands.Representation.Geometric.RepresentedGeometricLemmaCompactHaar
import Langlands.Representation.Geometric.RepresentedGeometricLemmaQuotientAction
import Langlands.Representation.Twist.IntertwiningProof

/-! # Original source coefficients of the represented compact integral -/

noncomputable section

universe u v

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactCoefficientAmbientTopology : TopologicalSpace (rationalPoints G) :=
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

local instance compactCoefficientCommonTargetTopology :
    TopologicalSpace (rationalPoints D.L') := leviPointTopology D.lQ' D.hlQ'

local notation "Kt" => geometricTargetIntersection (pointImage (lQ ≫ q)) (pointImage p) z⁻¹
local notation "dt" => targetPoints_isSemidirectDecomposition D
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "sQ" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "NQH" => Subgroup.comap (Subgroup.subtype H) (MonoidHom.ker π)
local notation "fH" => stabilizerToLeviPoints p l r hp hr hl hmul q z
local notation "χ" => SmoothCharacter.toMonoidHom
  (leviInducingHalfCharacter p l r hp hr hl)
local notation "Rs" => pointImage (D.r' ≫ D.p')
local notation "Hs" => pointImage (D.l' ≫ D.p')
local notation "hHs" => pointImage_le_normalizer D.p' D.l' D.r' D.hr'
local notation "eM" => MonoidHom.rangeRestrict (rationalPoints.map (D.l' ≫ D.p'))

/-- The original common-Levi projection of the full literal target intersection. -/
def compactTargetLeviProjection : Kt →* rationalPoints D.L' :=
  D.targetLeviPointsEquiv.symm.toMonoidHom.comp (dt).projection

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The source projection of the full target section is the original
common-Levi projection followed by the supplied original conjugation map. -/
theorem compactSectionSourceProjection (x : Kt) :
    letI := leviPointTopology l hl
    fH (D.targetParabolicPointsToStabilizer x) =
      rationalPoints.map (D.l' ≫ D.p') (D.e (D.compactTargetLeviProjection x)) := by
  let := leviPointTopology l hl
  have hc := D.stabilizerToLeviPoints_commonLeviToStabilizer
    (D.compactTargetLeviProjection x)
  change (leviPointsEquiv p l hp hl).symm
    (D.targetParabolicPointsToSourceLevi
      (Subgroup.inclusion (dt).levi_le
        (D.targetLeviPointsEquiv (D.compactTargetLeviProjection x)))) = _ at hc
  rw [D.targetParabolicPointsToSourceLevi_eq] at hc
  change (leviPointsEquiv p l hp hl).symm
    (D.targetLeviPointsToSourceLevi
      ((dt).projection ⟨D.targetLeviPointsEquiv (D.compactTargetLeviProjection x), _⟩)) = _ at hc
  rw [IsSemidirectDecomposition.projection_levi] at hc
  change (leviPointsEquiv p l hp hl).symm
    (D.targetLeviPointsToSourceLevi
      (D.targetLeviPointsEquiv (D.targetLeviPointsEquiv.symm ((dt).projection x)))) = _ at hc
  rw [D.targetLeviPointsEquiv.apply_symm_apply] at hc
  change (leviPointsEquiv p l hp hl).symm (D.targetParabolicPointsToSourceLevi x) = _
  rw [D.targetParabolicPointsToSourceLevi_eq]
  exact hc

variable (A : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M))

/-- The original source inducing half on the full target intersection. -/
def compactSourceHalfCharacter :
    letI := leviPointTopology l hl
    Kt →* ℂˣ := by
  letI := leviPointTopology l hl
  exact (χ).comp ((rationalPoints.map (D.l' ≫ D.p')).comp
    (D.e.toMonoidHom.comp D.compactTargetLeviProjection))

/-- The ordinary original source-radical quotient with its original
source inducing half, acted on by the whole literal target intersection. -/
def compactSourceQuotientAction :
    letI := leviPointTopology l hl
    Representation ℂ Kt (Jacquet.Localization.Coinvariants A.representation Rs 1) := by
  letI := leviPointTopology l hl
  exact Langlands.twist D.compactSourceHalfCharacter
    ((Jacquet.Localization.action A.representation Rs 1 Hs hHs
      (Jacquet.Localization.isInvariant_one Rs Hs hHs)).comp
      ((eM).comp (D.e.toMonoidHom.comp D.compactTargetLeviProjection)))

local notation "S" => compactComparisonSaturation D
local notation "hker" => projectionKernel_le_compactComparisonSaturation D
local notation "rS" => splitStagesRetraction π sQ
  (fun m => IsSemidirectDecomposition.projection_levi dQ m) S hker
local notation "sS" => MonoidHom.subgroupComap sQ S
local notation "HS" => Subgroup.subgroupOf H S
local notation "hSI" => compactComparisonSaturation_section_mem_stabilizer D
local notation "j" => MonoidHom.subgroupComap (Subgroup.subtype (MonoidHom.ker rS)) HS
local notation "σ" => Rep.ρ
  (Functor.obj (stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z) A)

namespace DynamicRealization

variable {D} (R : D.DynamicRealization)

local notation "hHS" => stabilizer_le_compactComparisonSaturation R
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHS)

/-- The actual nested integral coefficient, reindexed to the whole literal
target intersection, with its original section action. -/
def compactNestedCoefficientAction :
    letI := leviPointTopology l hl
    Representation ℂ Kt
      (Representation.Coinvariants (((σ).comp φ).comp j)) := by
  letI := leviPointTopology l hl
  exact (splitKernelCoefficientAction rS sS HS hSI ((σ).comp φ)).comp
    D.compactComparisonLeviEquiv.symm.toMonoidHom

/-- Removing the nested intersection and using the proved original
radical-image inclusion identifies the full target coefficient actions. -/
def compactNestedCoefficientSourceEquiv :
    letI := leviPointTopology l hl
    (R.compactNestedCoefficientAction A).Equiv (D.compactSourceQuotientAction A) := by
  letI := leviPointTopology l hl
  exact {
  toLinearEquiv :=
    (splitStagesCoefficientEquiv π sQ
      (fun m => IsSemidirectDecomposition.projection_levi dQ m)
      S H hker hHS σ).trans
        (D.stabilizerCoinvariantsSourceEquiv R.stabilizerKernel_image_le_sourceRadical A)
  isIntertwining' x := by
    apply Representation.Coinvariants.hom_ext
    ext a
    change A at a
    change D.stabilizerCoinvariantsSourceEquiv R.stabilizerKernel_image_le_sourceRadical A
      (Jacquet.mk σ NQH
        (((χ) (fH (D.targetParabolicPointsToStabilizer x)) : ℂ) •
          A.representation (fH (D.targetParabolicPointsToStabilizer x)) a)) = _
    simp only [D.compactSectionSourceProjection, map_smul,
      D.stabilizerCoinvariantsSourceEquiv_mk]
    rfl }

@[simp] theorem compactNestedCoefficientSourceEquiv_mk (a : A) :
    letI := leviPointTopology l hl
    R.compactNestedCoefficientSourceEquiv A
      (Representation.Coinvariants.mk (((σ).comp φ).comp j) a) =
        Jacquet.Localization.mk A.representation Rs 1 a := rfl

/-- The same class-preserving comparison retains the exact scalar character
of the compact integral. Normalization cancellation is a separate step. -/
def compactIntegralCoefficientSourceEquiv :
    letI := leviPointTopology l hl
    (Langlands.twist D.compactIntegralHaarCharacter (R.compactNestedCoefficientAction A)).Equiv
      (Langlands.twist D.compactIntegralHaarCharacter (D.compactSourceQuotientAction A)) := by
  letI := leviPointTopology l hl
  exact Langlands.twistEquiv D.compactIntegralHaarCharacter (R.compactNestedCoefficientSourceEquiv A)

@[simp] theorem compactIntegralCoefficientSourceEquiv_mk (a : A) :
    letI := leviPointTopology l hl
    R.compactIntegralCoefficientSourceEquiv A
      (Representation.Coinvariants.mk (((σ).comp φ).comp j) a) =
        Jacquet.Localization.mk A.representation Rs 1 a := rfl

variable {A}

/-- The actual nested coefficient quotient map of every source intertwiner. -/
def compactNestedCoefficientMap
    {B : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M)} (T : A ⟶ B) :
    letI := leviPointTopology l hl
    (R.compactNestedCoefficientAction A).IntertwiningMap
      (R.compactNestedCoefficientAction B) := by
  letI := leviPointTopology l hl
  exact {
  toLinearMap := Representation.Coinvariants.map _ _
    (splitStagesIntersectionMap π sQ
      (fun m => IsSemidirectDecomposition.projection_levi dQ m)
      S H hker hHS
      (((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).map T).hom))
  isIntertwining' x := by
    apply Representation.Coinvariants.hom_ext
    ext a
    exact congrArg (Representation.Coinvariants.mk _)
      (LinearMap.congr_fun
        (((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).map T).hom.isIntertwining'
          (D.targetParabolicPointsToStabilizer x)) a) }

/-- Every original source morphism commutes with the full coefficient
equivalence, using the actual original Jacquet map on the target. -/
theorem compactNestedCoefficientSourceEquiv_natural
    {B : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M)} (T : A ⟶ B)
    (x : letI := leviPointTopology l hl;
      Representation.Coinvariants (((σ).comp φ).comp j)) :
    letI := leviPointTopology l hl
    R.compactNestedCoefficientSourceEquiv B (R.compactNestedCoefficientMap T x) =
      Jacquet.Localization.mapLinear Rs 1 (SmoothRep.hom T)
        (R.compactNestedCoefficientSourceEquiv A x) := by
  let := leviPointTopology l hl
  induction x using Representation.Coinvariants.induction_on with
  | h a => rfl

/-- The scalar-twisted equivalence is natural by the same original
coefficient maps; twisting leaves their linear maps unchanged. -/
theorem compactIntegralCoefficientSourceEquiv_natural
    {B : letI := leviPointTopology l hl; SmoothRep.{0,u,v} ℂ (rationalPoints M)} (T : A ⟶ B)
    (x : letI := leviPointTopology l hl;
      Representation.Coinvariants (((σ).comp φ).comp j)) :
    letI := leviPointTopology l hl
    R.compactIntegralCoefficientSourceEquiv B
        (Langlands.twistIntertwining D.compactIntegralHaarCharacter
          (R.compactNestedCoefficientMap T) x) =
      Jacquet.Localization.mapLinear Rs 1 (SmoothRep.hom T)
        (R.compactIntegralCoefficientSourceEquiv A x) := by
  let := leviPointTopology l hl
  exact R.compactNestedCoefficientSourceEquiv_natural T x

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
