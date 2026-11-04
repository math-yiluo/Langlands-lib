import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCompact
import Langlands.Representation.Aubert.General.RationalGeometricTargetEpsilonFactorization

/-! # The original normalized coefficient and both epsilon corrections -/

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

private theorem normalizedCoefficient_units_identity (u v a b c : ℂˣ) :
    u / (a ^ 2 * c ^ 2) * v =
      (v * b⁻¹ * c⁻¹ * (u * a⁻¹ * c⁻¹)) * (b * a⁻¹) := by
  calc
    _ = (u * v) * (a⁻¹ * a⁻¹ * c⁻¹ * c⁻¹) := by
      simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
      ac_rfl
    _ = ((u * v) * (a⁻¹ * a⁻¹ * c⁻¹ * c⁻¹)) * (b⁻¹ * b) := by
      rw [inv_mul_cancel, mul_one]
    _ = _ := by ac_rfl

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

local notation "A" => RationalPoint k G.X
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "PJ" => parabolic i ν J
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ (n : A)) MI
local notation "Ls" => Subgroup.subgroupOf (geometricSourceIntersection MI MJ (n : A)) MJ
local notation "K" => Subgroup.subgroupOf (geometricTargetIntersection MI PJ (n : A)) MI
local notation "c" => geometricCommonLeviInTarget i ν I J dJ n
local notation "e" => geometricIntersectionSubgroupEquiv MI MJ (n : A)
local notation "p" => geometricCoefficientLeviMap MI PJ MJ UJ (n : A) hTarget

/-- The actual coefficient projection restricts to inverse conjugation on
the literal common Levi, with both nested subgroup copies retained. -/
theorem geometricCoefficientLeviMap_commonLevi :
    (p).comp c = (e).toMonoidHom := by
  apply MonoidHom.ext
  intro l
  change e (hTarget.projection (c l)) = e l
  rw [show hTarget.projection (c l) = l from hTarget.projection_levi l]

section Haar

variable [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))

local notation "χ" => HaarModulus.closedHalfCharacter UJ hUJ MJ dJ.levi_le_normalizer
local notation "χp" => MonoidHom.comp (MonoidHom.comp χ (Subgroup.subtype Ls)) p
local notation "δU" => geometricCompactRadicalModulus i ν I J dI n hUI
local notation "δD" => geometricCompactCorrectionModulus i ν I J dI n hUI hPJ
local notation "δu" => geometricTargetCorrectionRadicalModulus
  MI MJ (n : A) UI hUI dI.levi_le_normalizer
local notation "δv" => geometricForwardSourceRadicalModulus MI MJ (n : A)
  UJ hUJ dJ.levi_le_normalizer

/-- The original inducing half, restricted through the actual coefficient
projection, is the half-modulus of the forward-conjugate original radical. -/
theorem geometricInducingHalfCharacter_commonLevi :
    (χp).comp c =
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δv) := by
  rw [← geometricSourceCorrectionRadicalModulus_eq_forward]
  apply MonoidHom.ext
  intro l
  have hpc := congrArg (fun q : Lt →* Ls => q l)
    (geometricCoefficientLeviMap_commonLevi i ν I J dJ n hTarget)
  change p (c l) = e l at hpc
  change χ (p (c l) : MJ) =
    Jacquet.complexCharacter
      (Jacquet.positiveHalfCharacter
        (geometricSourceCorrectionRadicalModulus MI MJ (n : A)
          UJ hUJ dJ.levi_le_normalizer)) l
  rw [hpc]
  rfl

variable
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  [SecondCountableTopology (RationalPoint k G.X)]
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))

local notation "hMIMI" => (fun _ hx => Subgroup.le_normalizer hx : MI ≤ Subgroup.normalizer MI)
local notation "hMJMJ" => (fun _ hx => Subgroup.le_normalizer hx : MJ ≤ Subgroup.normalizer MJ)
local notation "δa" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  UI MJ hUI hMJ dI.levi_le_normalizer hMJMJ
local notation "δb" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  MI UJ hMI hUJ hMIMI dJ.levi_le_normalizer
local notation "δc" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  UI UJ hUI hUJ dI.levi_le_normalizer dJ.levi_le_normalizer
local notation "η" => geometricNormalizedCompactCharacter
  i ν I J dI dJ n hUI hUJ hPJ hTarget

/-- The remaining target-positive/source-inverse half-character ratio on the
literal common Levi, before either epsilon correction is cancelled. -/
def geometricNormalizedCompactEndpointRatioCharacter : Lt →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δb) *
    Jacquet.inverseHalfCharacter δa

include hStandard hG hi hν hN

/-- Restriction of the exact compact coefficient to the entire common Levi:
the two original radical halves and both full correction factors remain. -/
theorem geometricNormalizedCompactCharacter_commonLevi
    (hpJ : Continuous dJ.projection) :
    (η).comp c =
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δu) /
        Jacquet.complexCharacter (δa * δc)) *
          Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δv) := by
  have hD :
      (δD).comp c = δa * δc := by
    rw [← geometricEpsilonTwo_correctionModulus_eq i ν I J dI dJ n hUI hPJ]
    exact geometricEpsilonTwo_correctionModulus_eq_mul
      i ν hStandard hG hi hν hN I J n dJ dI hUI hPJ hMJ hUJ hpJ
  have hu := geometricEpsilonTwo_radicalModulus_eq i ν I J dI dJ n hUI
  have hv := geometricInducingHalfCharacter_commonLevi i ν I J dJ n hTarget hUJ
  apply MonoidHom.ext
  intro l
  have hDl := congrArg (fun q : Lt →* ℝ≥0ˣ => q l) hD
  have hul := congrArg (fun q : Lt →* ℝ≥0ˣ => q l) hu
  have hvl := congrArg (fun q : Lt →* ℂˣ => q l) hv
  change χp (c l) =
    Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δv) l at hvl
  change
    (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) (c l) /
      Jacquet.complexCharacter δD (c l)) * χp (c l) =
    (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δu) l /
      Jacquet.complexCharacter (δa * δc) l) *
        Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δv) l
  simp only [MonoidHom.comp_apply] at hDl hul
  rw [hvl]
  apply congrArg (fun z : ℂˣ =>
    z * Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δv) l)
  apply congrArg₂ (fun x y : ℂˣ => x / y)
  · change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        ((Units.map NNReal.sqrtHom.toMonoidHom) (δU (c l))) = _
    rw [← hul]
    rfl
  · change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        (δD (c l)) = _
    rw [hDl]
    rfl

/-- The original compact coefficient on the common Levi equals both original
epsilon corrections times the positive-target/inverse-source endpoint ratio.
No distinct-radical balance is assumed. -/
theorem geometricNormalizedCompactCharacter_commonLevi_eq_epsilonProduct
    (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection) :
    (η).comp c =
      (geometricEpsilonOne i ν I J dI dJ n hUJ hPI *
        geometricEpsilonTwo i ν I J dI dJ n hUI hPJ) *
        geometricNormalizedCompactEndpointRatioCharacter
          i ν I J dI dJ n hUI hUJ hMI hMJ := by
  unfold geometricNormalizedCompactEndpointRatioCharacter
  rw [geometricNormalizedCompactCharacter_commonLevi
    i ν I J dI dJ n hTarget hUI hUJ hPJ hStandard hG hi hν hN hMJ hpJ,
    geometricEpsilonOne_eq_factorized_half
      i ν hStandard hG hi hν hN I J dI dJ n hPI hMI hUI hUJ hpI,
    geometricEpsilonTwo_eq_factorized_half
      i ν hStandard hG hi hν hN I J n dJ dI hUI hPJ hMJ hUJ hpJ]
  apply MonoidHom.ext
  intro l
  have hsq (δ : Lt →* ℝ≥0ˣ) :
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ) l ^ 2 =
        Jacquet.complexCharacter δ l := by
    simpa only [Jacquet.complexCharacter, MonoidHom.comp_apply, map_pow] using
      congrArg (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        (Jacquet.positiveHalfCharacter_sq δ l)
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply, Jacquet.inverseHalfCharacter,
    MonoidHom.inv_apply, Jacquet.complexCharacter, MonoidHom.comp_apply, map_mul]
  have ha := hsq δa
  have hc := hsq δc
  simp only [Jacquet.complexCharacter, MonoidHom.comp_apply] at ha hc
  rw [← ha, ← hc]
  exact normalizedCoefficient_units_identity _ _ _ _ _

end Haar

end Langlands.Aubert.General.RationalPointFamily
