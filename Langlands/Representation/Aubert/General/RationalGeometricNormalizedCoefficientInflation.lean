import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCoefficientCharacter

/-! # Inflation of the original normalized coefficient from the common Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

private theorem character_eq_comp_of_radical
    {B L D : Type*} [Group B] [Group L] [Group D]
    (f : B →* D) (s : L →* B) (π : B →* L) (R : Subgroup B)
    (hf : ∀ r : R, f (r : B) = 1)
    (hr : ∀ x : B, (s (π x))⁻¹ * x ∈ R) :
    f = (f.comp s).comp π := by
  apply MonoidHom.ext
  intro x
  have h := hf ⟨(s (π x))⁻¹ * x, hr x⟩
  change f ((s (π x))⁻¹ * x) = 1 at h
  rw [map_mul, map_inv] at h
  exact (inv_mul_eq_one.mp h).symm

private theorem semidirect_character_eq_comp
    {B D : Type*} [Group B] [Group D] {P M U : Subgroup B}
    (h : IsSemidirectDecomposition P M U) (f : P →* D)
    (hf : ∀ r : U.subgroupOf P, f (r : P) = 1) :
    f = (f.comp (Subgroup.inclusion h.levi_le)).comp h.projection := by
  exact character_eq_comp_of_radical f (Subgroup.inclusion h.levi_le)
    h.projection (U.subgroupOf P) hf (fun x => h.projection_inv_mul_mem x)

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν J))

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
local notation "Rk" => Subgroup.subgroupOf Rt K
local notation "c" => geometricCommonLeviInTarget i ν I J dJ n
local notation "p" => geometricCoefficientLeviMap MI PJ MJ UJ (n : A) hTarget
local notation "χ" => HaarModulus.closedHalfCharacter UJ hUJ MJ dJ.levi_le_normalizer
local notation "χp" => MonoidHom.comp (MonoidHom.comp χ (Subgroup.subtype Ls)) p
local notation "δU" => geometricCompactRadicalModulus i ν I J dI n hUI
local notation "δD" => geometricCompactCorrectionModulus i ν I J dI n hUI hPJ
local notation "η" => geometricNormalizedCompactCharacter
  i ν I J dI dJ n hUI hUJ hPJ hTarget

omit [LocallyCompactSpace (RationalPoint k G.X)] in
include hMI hUJc in
/-- The literal target radical inside the original target Levi is a limit
of compact subgroups, by forward conjugation and closed intersection. -/
theorem isLimitOfCompactSubgroups_geometricTargetRadical :
    Jacquet.Localization.IsLimitOfCompactSubgroups Rt := by
  simpa only [geometricSourceIntersection, geometricTargetIntersection, inv_inv] using
    (isLimitOfCompactSubgroups_geometricSourceIntersection
      UJ MI (n : A)⁻¹ hMI hUJc)

include hMI hUJc in
/-- Every remaining factor of the original coefficient is trivial on the
literal target radical, including its nested copy inside the target parabolic. -/
theorem geometricNormalizedCompactCharacter_eq_one_on_radical (r : Rk) :
    η r = 1 := by
  have hRc : Jacquet.Localization.IsLimitOfCompactSubgroups Rk :=
    isLimitOfCompactSubgroups_subgroupOf Rt K
      ((isClosed_geometricTargetIntersection MI PJ hMI hPJ (n : A)).preimage
        continuous_subtype_val)
      (isLimitOfCompactSubgroups_geometricTargetRadical i ν I J n hMI hUJc)
  have hu := positiveCharacter_eq_one_on_compactLimit δU
    (isOpen_ker_geometricCompactRadicalModulus i ν I J dI n hUI) Rk hRc r
  have hd := positiveCharacter_eq_one_on_compactLimit δD
    (isOpen_ker_geometricCompactCorrectionModulus i ν I J dI n hUI hPJ) Rk hRc r
  have hp : p (r : K) = 1 := by
    change geometricIntersectionSubgroupEquiv MI MJ (n : A)
      (hTarget.projection (r : K)) = 1
    rw [(hTarget.projection_eq_one_iff (r : K)).mpr r.property, map_one]
  change (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) r /
    Jacquet.complexCharacter δD r) * χp r = 1
  simp only [Jacquet.complexCharacter, Jacquet.positiveHalfCharacter,
    MonoidHom.comp_apply, hu, hd, hp, map_one, div_one, mul_one]

include hMI hUJc in
/-- The original full-intersection character is inflated from its actual
restriction to the common Levi through the original target projection. -/
theorem geometricNormalizedCompactCharacter_eq_projection :
    η = ((η).comp c).comp hTarget.projection := by
  have hc : c = Subgroup.inclusion hTarget.levi_le := rfl
  rw [hc]
  exact semidirect_character_eq_comp hTarget η
    (geometricNormalizedCompactCharacter_eq_one_on_radical
      i ν I J dI dJ n hTarget hUI hUJ hPJ hMI hUJc)

variable (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))

/-- Both original epsilon corrections times the remaining original endpoint
ratio, inflated to the entire literal target intersection. -/
def geometricNormalizedCompactInflatedCharacter : K →* ℂˣ :=
  ((geometricEpsilonOne i ν I J dI dJ n hUJ hPI *
    geometricEpsilonTwo i ν I J dI dJ n hUI hPJ) *
      geometricNormalizedCompactEndpointRatioCharacter
        i ν I J dI dJ n hUI hUJ hMI hMJ).comp hTarget.projection

variable (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  [SecondCountableTopology (RationalPoint k G.X)]

include hMI hUJc hStandard hG hi hν hN in
/-- The exact epsilon-product factorization holds on the whole original
target intersection, without a whole-common-Levi balance premise. -/
theorem geometricNormalizedCompactCharacter_eq_inflated
    (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection) :
    η = geometricNormalizedCompactInflatedCharacter
      i ν I J dI dJ n hTarget hUI hUJ hPJ hMI hPI hMJ := by
  rw [geometricNormalizedCompactCharacter_eq_projection
    i ν I J dI dJ n hTarget hUI hUJ hPJ hMI hUJc,
    geometricNormalizedCompactCharacter_commonLevi_eq_epsilonProduct
      i ν I J dI dJ n hTarget hUI hUJ hPJ hStandard hG hi hν hN
      hPI hMI hMJ hpI hpJ]
  rfl

end Langlands.Aubert.General.RationalPointFamily
