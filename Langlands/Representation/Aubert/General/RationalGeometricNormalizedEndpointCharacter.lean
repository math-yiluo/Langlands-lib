import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCoefficientInflation
import Langlands.Representation.Aubert.General.GeometricTermNormalization

/-! # Actual source and target endpoint half-characters of the compact coefficient -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General

section Source

variable {A : Type*} [Group A] [TopologicalSpace A] [LocallyCompactSpace A]
  [IsTopologicalGroup A]
  (MI MJ UI : Subgroup A) (n : A)
  (hUI : IsClosed (UI : Set A)) (hMJ : IsClosed (MJ : Set A))
  (hMIUI : MI ≤ Subgroup.normalizer UI)
  (hLsS : (geometricSourceIntersection MI MJ n).subgroupOf MJ ≤
    Subgroup.normalizer ((geometricSourceIntersection UI MJ n).subgroupOf MJ))

local notation "S0" => geometricSourceIntersection UI MJ n
local notation "Ls0" => geometricSourceIntersection MI MJ n
local notation "Lt0" => geometricTargetIntersection MI MJ n
local notation "Ls" => Subgroup.subgroupOf Ls0 MJ
local notation "Lt" => Subgroup.subgroupOf Lt0 MI
local notation "e" => geometricIntersectionSubgroupEquiv MI MJ n

/-- The original inside source Jacquet inverse half-character. -/
def geometricSourceEndpointInverseHalfCharacter : Ls →* ℂˣ :=
  letI := hMJ.locallyCompactSpace
  HaarModulus.closedInverseHalfCharacter
    ((S0).subgroupOf MJ)
    ((isClosed_geometricSourceIntersection UI MJ hUI hMJ n).preimage
      continuous_subtype_val)
    Ls hLsS

include hMIUI in
/-- The original source inverse half transports to the inverse half of the
forward source-endpoint intersection modulus on the literal common Levi. -/
theorem geometricSourceEndpointInverseHalfCharacter_transport :
    (geometricSourceEndpointInverseHalfCharacter MI MJ UI n hUI hMJ hLsS).comp
        (e).toMonoidHom =
      Jacquet.inverseHalfCharacter
        (geometricCommonLeviIntersectionModulus MI MJ n UI MJ hUI hMJ
          hMIUI (fun _ hx => Subgroup.le_normalizer hx)) := by
  let _ := hMJ.locallyCompactSpace
  let hS := isClosed_geometricSourceIntersection UI MJ hUI hMJ n
  let hF := isClosed_geometricTargetIntersection UI MJ hUI hMJ n
  let hSL := normalizes_of_subgroupOf
    (inf_le_left : S0 ≤ MJ) (inf_le_left : Ls0 ≤ MJ) hLsS
  let hFL := geometricCommonLevi_normalizes_intersection MI MJ UI MJ n hMIUI
    (fun _ hx => Subgroup.le_normalizer hx)
  apply MonoidHom.ext
  intro l
  have he :
      subgroupOfContinuousEquiv (inf_le_left : Ls0 ≤ MJ) (e l) =
        conjugationEquiv n (geometricIntersectionMembership MI MJ n)
          (subgroupOfContinuousEquiv (inf_le_left : Lt0 ≤ MI) l) := by
    apply Subtype.ext
    exact geometricIntersectionSubgroupEquiv_apply MI MJ n l
  calc
    _ = HaarModulus.closedInverseHalfCharacter S0 hS Ls0 hSL
        (subgroupOfContinuousEquiv (inf_le_left : Ls0 ≤ MJ) (e l)) :=
      closedInverseHalfCharacter_subgroupOf hMJ hS inf_le_left inf_le_left hSL (e l)
    _ = HaarModulus.closedInverseHalfCharacter S0 hS Ls0 hSL
        (conjugationEquiv n (geometricIntersectionMembership MI MJ n)
          (subgroupOfContinuousEquiv (inf_le_left : Lt0 ≤ MI) l)) :=
      congrArg (HaarModulus.closedInverseHalfCharacter S0 hS Ls0 hSL) he
    _ = HaarModulus.closedInverseHalfCharacter
        (geometricTargetIntersection UI MJ n) hF Lt0 hFL
        (subgroupOfContinuousEquiv (inf_le_left : Lt0 ≤ MI) l) :=
      (closedInverseHalfCharacter_conj n
        (geometricIntersectionMembership UI MJ n)
        (geometricIntersectionMembership MI MJ n) hS hF hSL hFL _).symm
    _ = _ := rfl

end Source

section Target

variable {A : Type*} [Group A] [TopologicalSpace A] [LocallyCompactSpace A]
  [IsTopologicalGroup A]
  (MI MJ UJ : Subgroup A) (n : A)
  (hMI : IsClosed (MI : Set A)) (hUJ : IsClosed (UJ : Set A))
  (hMJUJ : MJ ≤ Subgroup.normalizer UJ)
  (hLtR : (geometricTargetIntersection MI MJ n).subgroupOf MI ≤
    Subgroup.normalizer ((geometricTargetIntersection MI UJ n).subgroupOf MI))

local notation "R0" => geometricTargetIntersection MI UJ n
local notation "L0" => geometricTargetIntersection MI MJ n
local notation "Lt" => Subgroup.subgroupOf L0 MI

/-- The original inside target induction positive half, restricted to its Levi. -/
def geometricTargetEndpointHalfCharacter : Lt →* ℂˣ :=
  letI := hMI.locallyCompactSpace
  HaarModulus.closedHalfCharacter
    ((R0).subgroupOf MI)
    ((isClosed_geometricTargetIntersection MI UJ hMI hUJ n).preimage
      continuous_subtype_val)
    Lt hLtR

include hMJUJ in
/-- The actual target endpoint half is the positive half of the literal
target-endpoint intersection modulus on the entire common Levi. -/
theorem geometricTargetEndpointHalfCharacter_eq :
    geometricTargetEndpointHalfCharacter MI MJ UJ n hMI hUJ hLtR =
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
        (geometricCommonLeviIntersectionModulus MI MJ n MI UJ hMI hUJ
          (fun _ hx => Subgroup.le_normalizer hx) hMJUJ)) := by
  let _ := hMI.locallyCompactSpace
  apply MonoidHom.ext
  intro l
  exact closedHalfCharacter_subgroupOf hMI
    (isClosed_geometricTargetIntersection MI UJ hMI hUJ n)
    inf_le_left inf_le_left
    (geometricCommonLevi_normalizes_intersection MI MJ MI UJ n
      (fun _ hx => Subgroup.le_normalizer hx) hMJUJ) l

end Target

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

local notation "A" => RationalPoint k G.X
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "PJ" => parabolic i ν J
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ (n : A)) MI
local notation "Ls" => Subgroup.subgroupOf (geometricSourceIntersection MI MJ (n : A)) MJ
local notation "K" => Subgroup.subgroupOf (geometricTargetIntersection MI PJ (n : A)) MI
local notation "Rt" => Subgroup.subgroupOf (geometricTargetIntersection MI UJ (n : A)) MI
local notation "p" => geometricCoefficientLeviMap MI PJ MJ UJ (n : A) hTarget
local notation "e" => geometricIntersectionSubgroupEquiv MI MJ (n : A)
local notation "χs" => geometricSourceEndpointInverseHalfCharacter
  MI MJ UI (n : A) hUI hMJ hSource.levi_le_normalizer
local notation "χt" => geometricTargetEndpointHalfCharacter
  MI MJ UJ (n : A) hMI hUJ hTarget.levi_le_normalizer

/-- The retained endpoint ratio is precisely the original target positive
half times the original transported source inverse half. -/
theorem geometricNormalizedCompactEndpointRatioCharacter_eq_endpoints :
    geometricNormalizedCompactEndpointRatioCharacter i ν I J dI dJ n hUI hUJ hMI hMJ =
      χt * (χs).comp (e).toMonoidHom := by
  rw [geometricSourceEndpointInverseHalfCharacter_transport
    MI MJ UI (n : A) hUI hMJ dI.levi_le_normalizer hSource.levi_le_normalizer,
    geometricTargetEndpointHalfCharacter_eq
      MI MJ UJ (n : A) hMI hUJ dJ.levi_le_normalizer hTarget.levi_le_normalizer]
  rfl

/-- The original target induction half on its entire parabolic intersection,
times the original source Jacquet inverse half through the actual coefficient map. -/
def geometricNormalizedCompactEndpointCharacter : K →* ℂˣ :=
  letI := hMI.locallyCompactSpace
  HaarModulus.closedHalfCharacter Rt
      ((isClosed_geometricTargetIntersection MI UJ hMI hUJ (n : A)).preimage
        continuous_subtype_val)
      K hTarget.le_normalizer *
    (χs).comp p

/-- Inflation of the endpoint ratio is the actual normalized endpoint character
on the entire target intersection; the radical is unimodular by compact limits. -/
theorem geometricNormalizedCompactEndpointRatioCharacter_inflate
    (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups UJ) :
    (geometricNormalizedCompactEndpointRatioCharacter
      i ν I J dI dJ n hUI hUJ hMI hMJ).comp hTarget.projection =
      geometricNormalizedCompactEndpointCharacter
        i ν I J n hUI hUJ hMI hMJ hSource hTarget := by
  rw [geometricNormalizedCompactEndpointRatioCharacter_eq_endpoints
    i ν I J dI dJ n hUI hUJ hMI hMJ hSource hTarget]
  let _ := hMI.locallyCompactSpace
  let hRt : IsClosed (Rt : Set MI) :=
    (isClosed_geometricTargetIntersection MI UJ hMI hUJ (n : A)).preimage
      continuous_subtype_val
  have hRc := isLimitOfCompactSubgroups_geometricTargetRadical i ν I J n hMI hUJc
  have ht := closedHalfCharacter_eq_comp_projection hTarget hRt
    (isUnimodularModulus_of_isLimitOfCompactSubgroups Rt hRt hRc)
  change (χt * (χs).comp (e).toMonoidHom).comp hTarget.projection =
    HaarModulus.closedHalfCharacter Rt hRt K hTarget.le_normalizer * (χs).comp p
  rw [ht]
  rfl

variable
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  [SecondCountableTopology (RationalPoint k G.X)]

include hStandard hG hi hν hN in
/-- The original normalized compact coefficient equals both original epsilon
corrections times the actual endpoint normalization on the entire intersection. -/
theorem geometricNormalizedCompactCharacter_eq_epsilonEndpoints
    (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups UJ)
    (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection) :
    geometricNormalizedCompactCharacter i ν I J dI dJ n hUI hUJ hPJ hTarget =
      (geometricEpsilonOne i ν I J dI dJ n hUJ hPI *
        geometricEpsilonTwo i ν I J dI dJ n hUI hPJ).comp hTarget.projection *
        geometricNormalizedCompactEndpointCharacter
          i ν I J n hUI hUJ hMI hMJ hSource hTarget := by
  rw [geometricNormalizedCompactCharacter_eq_inflated
    i ν I J dI dJ n hTarget hUI hUJ hPJ hMI hUJc hPI hMJ
      hStandard hG hi hν hN hpI hpJ]
  unfold geometricNormalizedCompactInflatedCharacter
  rw [MonoidHom.mul_comp,
    geometricNormalizedCompactEndpointRatioCharacter_inflate
      i ν I J dI dJ n hUI hUJ hMI hMJ hSource hTarget hUJc]

end RationalPointFamily
end Langlands.Aubert.General
