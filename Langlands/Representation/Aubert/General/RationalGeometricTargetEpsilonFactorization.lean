import Langlands.Representation.Aubert.General.RationalGeometricEpsilonFactorization
import Langlands.Representation.Aubert.General.RationalGeometricRefinedIntersection

/-! # Factorization of the original rational target epsilon -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))

local notation "A" => RationalPoint k G.X
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "PJ" => parabolic i ν J
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "Q" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (n : A))) (parabolic i ν J)
local notation "N" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (n : A))) (levi i ν J)
local notation "V" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (n : A))) (unipotent i ν J)

include hStandard hG hi hν hN dJ

/-- The literal target correction intersection has the original source
endpoint and common radical as its two semidirect factors. -/
theorem geometricTargetCorrectionIntersectionDecomposition :
    IsSemidirectDecomposition
      (geometricTargetIntersection UI PJ (n : A))
      (geometricTargetIntersection UI MJ (n : A))
      (geometricTargetIntersection UI UJ (n : A)) :=
  RefinedIntersection.innerDecomposition UI Q N V
    (geometricUnipotentParabolic_eq_mul i ν hStandard hG hi hν hN I J n)
    (dJ.forwardConjugate (n : A))

/-- The target correction projection is continuous whenever the original
inducing-side projection is continuous. -/
theorem continuous_geometricTargetCorrectionIntersection_projection
    (hpJ : Continuous dJ.projection) :
    Continuous (geometricTargetCorrectionIntersectionDecomposition
      i ν hStandard hG hi hν hN I J n dJ).projection :=
  RefinedIntersection.continuous_inner_projection UI Q N V
    (geometricUnipotentParabolic_eq_mul i ν hStandard hG hi hν hN I J n)
    (dJ.forwardConjugate (n : A))
    (dJ.continuous_forwardConjugate_projection hpJ (n : A))

/-- Actual multiplication coordinates, with no change of the target point. -/
def geometricTargetCorrectionIntersectionCoordinates
    (hpJ : Continuous dJ.projection) :
    geometricTargetIntersection UI MJ (n : A) ×
        geometricTargetIntersection UI UJ (n : A) ≃ₜ
      geometricTargetIntersection UI PJ (n : A) :=
  (geometricTargetCorrectionIntersectionDecomposition
    i ν hStandard hG hi hν hN I J n dJ).coordinates
      (continuous_geometricTargetCorrectionIntersection_projection
        i ν hStandard hG hi hν hN I J n dJ hpJ)

@[simp] theorem geometricTargetCorrectionIntersectionCoordinates_apply
    (hpJ : Continuous dJ.projection)
    (a : geometricTargetIntersection UI MJ (n : A))
    (c : geometricTargetIntersection UI UJ (n : A)) :
    (geometricTargetCorrectionIntersectionCoordinates
      i ν hStandard hG hi hν hN I J n dJ hpJ (a, c) : A) =
      (a : A) * (c : A) := rfl

section Haar

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [SecondCountableTopology (RationalPoint k G.X)]
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))

local notation "L" => geometricTargetIntersection MI MJ (n : A)
local notation "Lt" => Subgroup.subgroupOf (geometricTargetIntersection MI MJ (n : A)) MI
local notation "hMJPJ" => dJ.levi_le.trans (fun _ hx => Subgroup.le_normalizer hx)
local notation "hMJMJ" => (fun _ hx => Subgroup.le_normalizer hx : MJ ≤ Subgroup.normalizer MJ)
local notation "hLP" => geometricCommonLevi_normalizes_intersection
  MI MJ UI PJ (n : A) dI.levi_le_normalizer hMJPJ
local notation "hLM" => geometricCommonLevi_normalizes_intersection
  MI MJ UI MJ (n : A) dI.levi_le_normalizer hMJMJ
local notation "hLU" => geometricCommonLevi_normalizes_intersection
  MI MJ UI UJ (n : A) dI.levi_le_normalizer dJ.levi_le_normalizer
local notation "deltaA" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  UI MJ hUI hMJ dI.levi_le_normalizer hMJMJ
local notation "deltaC" => geometricCommonLeviIntersectionModulus MI MJ (n : A)
  UI UJ hUI hUJ dI.levi_le_normalizer dJ.levi_le_normalizer
local notation "deltaU" => geometricTargetCorrectionRadicalModulus
  MI MJ (n : A) UI hUI dI.levi_le_normalizer

/-- The target correction Haar modulus is the product of the actual source
endpoint and common radical moduli on every common-Levi point. -/
theorem geometricTargetCorrectionIntersection_modulus_eq_mul
    (hpJ : Continuous dJ.projection) :
    HaarModulus.closedRestrictCharacter
        (geometricTargetIntersection UI PJ (n : A))
        (isClosed_geometricTargetIntersection UI PJ hUI hPJ (n : A)) L hLP =
      HaarModulus.closedRestrictCharacter
        (geometricTargetIntersection UI MJ (n : A))
        (isClosed_geometricTargetIntersection UI MJ hUI hMJ (n : A)) L hLM *
      HaarModulus.closedRestrictCharacter
        (geometricTargetIntersection UI UJ (n : A))
        (isClosed_geometricTargetIntersection UI UJ hUI hUJ (n : A)) L hLU := by
  apply MonoidHom.ext
  intro l
  exact (geometricTargetCorrectionIntersectionDecomposition
    i ν hStandard hG hi hν hN I J n dJ).closedNormalizerCharacter_eq_mul
      (continuous_geometricTargetCorrectionIntersection_projection
        i ν hStandard hG hi hν hN I J n dJ hpJ)
      (isClosed_geometricTargetIntersection UI PJ hUI hPJ (n : A))
      (isClosed_geometricTargetIntersection UI MJ hUI hMJ (n : A))
      (isClosed_geometricTargetIntersection UI UJ hUI hUJ (n : A))
      (l : A) (hLP l.property) (hLM l.property) (hLU l.property)

/-- Factor the original target correction modulus on the literal nested
common Levi, retaining its original ambient point. -/
theorem geometricEpsilonTwo_correctionModulus_eq_mul
    (hpJ : Continuous dJ.projection) :
    geometricTargetCorrectionIntersectionModulus MI MJ (n : A)
        UI PJ hUI hPJ dI.levi_le_normalizer hMJPJ =
      deltaA * deltaC := by
  rw [geometricTargetCorrectionIntersectionModulus_eq_forward]
  have h := geometricTargetCorrectionIntersection_modulus_eq_mul
    i ν hStandard hG hi hν hN I J n dJ dI hUI hPJ hMJ hUJ hpJ
  apply MonoidHom.ext
  intro l
  exact congrArg (fun f : L →* ℝ≥0ˣ =>
    f ((Subgroup.subgroupOfEquivOfLe
      (inf_le_left : geometricTargetIntersection MI MJ (n : A) ≤ MI)) l)) h

/-- The original target epsilon has its canonical positive target-radical
half and both inverse intersection halves on the entire literal common Levi. -/
theorem geometricEpsilonTwo_eq_factorized_half
    (hpJ : Continuous dJ.projection) :
    geometricEpsilonTwo i ν I J dI dJ n hUI hPJ =
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaU) *
        Jacquet.inverseHalfCharacter deltaA * Jacquet.inverseHalfCharacter deltaC := by
  unfold geometricEpsilonTwo
  rw [geometricTargetCorrectionCharacter_eq,
    geometricEpsilonTwo_correctionModulus_eq_mul
      i ν hStandard hG hi hν hN I J n dJ dI hUI hPJ hMJ hUJ hpJ]
  apply MonoidHom.ext
  intro l
  simp only [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, MonoidHom.mul_apply,
    MonoidHom.inv_apply, map_mul, mul_inv, mul_assoc]

end Haar

end Langlands.Aubert.General.RationalPointFamily
