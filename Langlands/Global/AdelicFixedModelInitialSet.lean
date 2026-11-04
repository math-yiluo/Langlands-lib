import Langlands.Global.AdelicFixedModelCocone

/-! # Enlarging the initial arithmetic model base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable {S U : Finset (AlgebraicCurve.Place k F)} (hSU : S ⊆ U)
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- Base change along the actual integer inclusion identifies full-adele points. -/
def curvePlaceFixedModelInitialSetEquiv :
    CurvePlaceFixedModelAdelePoints k F S X ≃
      CurvePlaceFixedModelAdelePoints k F U (curvePlaceLevelModelBaseChange k F hSU X) := by
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F U) :=
    (curvePlaceSIntegersMap k F hSU).toAlgebra
  letI : Algebra (curvePlaceSIntegers k F U) (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F U) (curvePlaceAdeleOver k F U))
  letI : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F U)
      (curvePlaceAdeleOver k F S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F U) (curvePlaceAdeleOver k F S) X

/-- The inverse comparison is the first projection from the actual base change. -/
@[simp]
theorem curvePlaceFixedModelInitialSetEquiv_symm_left
    (p : CurvePlaceFixedModelAdelePoints k F U (curvePlaceLevelModelBaseChange k F hSU X)) :
    ((curvePlaceFixedModelInitialSetEquiv k F hSU X).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))) := by
  let algSU : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F U) :=
    (curvePlaceSIntegersMap k F hSU).toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algUA : Algebra (curvePlaceSIntegers k F U) (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F U) (curvePlaceAdeleOver k F U))
  let tower : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F U)
      (curvePlaceAdeleOver k F S) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSU algUA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv_symm_left (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F U) _ _ algSU (curvePlaceAdeleOver k F S)
    (curvePlaceAdeleOver k F S).commRing algSA algUA tower X p

/-- The comparison preserves the underlying point of the original model. -/
@[simp]
theorem curvePlaceFixedModelInitialSetEquiv_left_fst
    (p : CurvePlaceFixedModelAdelePoints k F S X) :
    (curvePlaceFixedModelInitialSetEquiv k F hSU X p).left ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))) = p.left := by
  exact (curvePlaceFixedModelInitialSetEquiv_symm_left k F hSU X _).symm.trans
    (congrArg (fun q => q.left)
      ((curvePlaceFixedModelInitialSetEquiv k F hSU X).symm_apply_apply p))

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable {S U : Finset (FinitePlace K)} (hSU : S ⊆ U)
variable (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))

/-- Base change along the actual integer inclusion identifies full-adele points. -/
def numberFieldFixedModelInitialSetEquiv :
    NumberFieldFixedModelAdelePoints K S X ≃
      NumberFieldFixedModelAdelePoints K U (numberFieldLevelModelBaseChange K hSU X) := by
  letI : Algebra (((S : Set (FinitePlace K)).integer K)) (((U : Set (FinitePlace K)).integer K)) :=
    (numberFieldSIntegersMap K hSU).toAlgebra
  letI : Algebra (((U : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra (((U : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K U))
  letI : IsScalarTower (((S : Set (FinitePlace K)).integer K)) (((U : Set (FinitePlace K)).integer K))
      (numberFieldAdeleOver K S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv (((S : Set (FinitePlace K)).integer K))
    (((U : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K S) X

/-- The inverse comparison is the first projection from the actual base change. -/
@[simp]
theorem numberFieldFixedModelInitialSetEquiv_symm_left
    (p : NumberFieldFixedModelAdelePoints K U (numberFieldLevelModelBaseChange K hSU X)) :
    ((numberFieldFixedModelInitialSetEquiv K hSU X).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))) := by
  let algSU : Algebra (((S : Set (FinitePlace K)).integer K)) (((U : Set (FinitePlace K)).integer K)) :=
    (numberFieldSIntegersMap K hSU).toAlgebra
  let algSA : Algebra (((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algUA : Algebra (((U : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra (((U : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K U))
  let tower : IsScalarTower (((S : Set (FinitePlace K)).integer K)) (((U : Set (FinitePlace K)).integer K))
      (numberFieldAdeleOver K S) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSU algUA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv_symm_left (((S : Set (FinitePlace K)).integer K))
    (((U : Set (FinitePlace K)).integer K)) _ _ algSU (numberFieldAdeleOver K S)
    (numberFieldAdeleOver K S).commRing algSA algUA tower X p

/-- The comparison preserves the underlying point of the original model. -/
@[simp]
theorem numberFieldFixedModelInitialSetEquiv_left_fst
    (p : NumberFieldFixedModelAdelePoints K S X) :
    (numberFieldFixedModelInitialSetEquiv K hSU X p).left ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))) = p.left := by
  exact (numberFieldFixedModelInitialSetEquiv_symm_left K hSU X _).symm.trans
    (congrArg (fun q => q.left)
      ((numberFieldFixedModelInitialSetEquiv K hSU X).symm_apply_apply p))

end NumberField

end Langlands.Global
