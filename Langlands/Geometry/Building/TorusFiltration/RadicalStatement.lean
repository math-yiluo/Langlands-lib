import Langlands.Geometry.Building.TorusFiltration.Points
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # The pro-unipotent term of the minimal congruent torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- The two descriptions of the strict-depth union at zero in KP Lemma
B.10.11 and its special-fibre image in Proposition B.10.12. -/
def MinimalCongruentZeroPlusStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp),
    let M := connectedNeronModel F T hT
    let P := minimalCongruentPlus F T hT 0
    P = (M.integralPoints : Set (rationalPoints T.toGrp)) ∩
      (⋃ r : Set.Ioi (0 : ℝ≥0),
        (localTorusFiltration F T hT r : Set (rationalPoints T.toGrp))) ∧
    ∃ (U : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : U ⟶ M.specialFibre), IsUnipotentRadical i ∧
        P = ↑(((rationalPoints.map i).range.comap M.reduction).map M.integralPointMap) ∧
        ∃ (Mplus : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp)
          (φ : Mplus.Hom M (𝟙 T.toGrp)), Mplus.IsSmooth ∧
            (Mplus.integralPoints : Set (rationalPoints T.toGrp)) = P ∧
              ∃ j : Mplus.specialFibre ⟶ U, j ≫ i = φ.specialFibreMap ∧
                Surjective j.hom.hom.left

/-- The unipotence assertion used at positive depths in the proofs of
KP Proposition B.10.12 and Corollary B.10.14. -/
def MinimalCongruentPositiveUnipotentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp),
    0 < r → M.IsSmooth → M.integralPoints = minimalCongruentPoints F T hT r →
      IsUnipotent M.specialFibre

end Langlands.Geometry.Building
