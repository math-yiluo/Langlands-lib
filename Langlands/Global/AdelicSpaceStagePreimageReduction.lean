import Langlands.Global.AdelicSpaceFullPreimageReduction
import Langlands.Global.AdelicSpaceModelOpenReduction

/-! # Exact preimages at every algebraic-space adelic stage -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

namespace AdelicSpacePreimageReduction

/-- A commuting equivalence square transports membership in the range. -/
theorem mem_range_iff_of_equiv {A B A' B' : Type*}
    (eA : A ≃ A') (eB : B ≃ B') (s : A → B) (s' : A' → B')
    (hs : ∀ a, eB (s a) = s' (eA a)) (b : B) :
    b ∈ Set.range s ↔ eB b ∈ Set.range s' := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨eA a, (hs a).symm⟩
  · rintro ⟨a', ha'⟩
    refine ⟨eA.symm a', eB.injective ?_⟩
    rw [hs, eA.apply_symm_apply]
    exact ha'

/-- Equivalences of both stage and full point spaces preserve exact range preimages. -/
theorem preimage_range_eq_of_equiv {A B P Q A' B' P' Q' : Type*}
    (eA : A ≃ A') (eB : B ≃ B') (eP : P ≃ P') (eQ : Q ≃ Q')
    (s : A → P) (t : B → Q) (s' : A' → P') (t' : B' → Q')
    (f : P → Q) (f' : P' → Q')
    (hs : ∀ a, eP (s a) = s' (eA a))
    (ht : ∀ b, eQ (t b) = t' (eB b))
    (hf : ∀ p, eQ (f p) = f' (eP p))
    (hpre : f' ⁻¹' Set.range t' = Set.range s') :
    f ⁻¹' Set.range t = Set.range s := by
  ext p
  change f p ∈ Set.range t ↔ p ∈ Set.range s
  rw [mem_range_iff_of_equiv eB eQ t t' ht,
    mem_range_iff_of_equiv eA eP s s' hs, hf]
  exact Set.ext_iff.mp hpre (eP p)

end AdelicSpacePreimageReduction

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (AlgebraicCurve.Place k F))

/-- Full adelic points commute with extending the model's integer base to `T`. -/
def curvePlaceSpaceAdeleLevelBaseChangeEquiv
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (T : AdelicLevelIndexAbove S) :
    CurvePlaceSpaceAdelePoints k F S X ≃
      CurvePlaceSpaceAdelePoints k F T.val
        (curvePlaceSpaceLevelBaseChange k F T.property X) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleOver k F S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) X).symm

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- The full-adele base-change identification is natural in the model morphism. -/
theorem curvePlaceSpaceAdeleLevelBaseChangeEquiv_map (T : AdelicLevelIndexAbove S)
    (f : X ⟶ Y) (p : CurvePlaceSpaceAdelePoints k F S X) :
    curvePlaceSpaceAdeleLevelBaseChangeEquiv k F S Y T (RingPoints.map f p) =
      RingPoints.map (curvePlaceSpaceLevelModelMap k F S T f)
        (curvePlaceSpaceAdeleLevelBaseChangeEquiv k F S X T p) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleOver k F S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) Y).symm
        (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val)) f)
      ((baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
        (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- Stage inclusion agrees with level inclusion after both base-change identifications. -/
theorem curvePlaceSpaceAdeleLevelBaseChangeEquiv_stageMap
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (T : AdelicLevelIndexAbove S)
    (p : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curvePlaceSpaceAdeleLevelBaseChangeEquiv k F S X T
        (curvePlaceSpaceStageMap k F S X T p) =
      RingPoints.changeRing (curvePlaceSpaceLevelInclusion k F T.val)
        (curvePlaceSpaceStageEquiv k F S X T p) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleOver k F S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F T.val]
      curvePlaceAdeleOver k F S :=
    { toRingHom := (curvePlaceAdeleLevel k F T.val).subtype, commutes' := fun _ => rfl }
  change (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) X).symm
        (RingPoints.changeRing (curvePlaceAdeleLevelOverι k F S T).hom p) =
    RingPoints.changeRing ψ
      ((baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
        (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_changeRing, Equiv.apply_symm_apply]
  rfl

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F]

/-- Exact preimages at every curve-place stage, with valuative existence and properness
of the base-changed morphism retained as explicit inputs. -/
theorem curvePlaceSpaceStagePreimage_of_valuative
    (hv : SpaceValuativeExistenceStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (f : X ⟶ Y) (T : AdelicLevelIndexAbove S)
    (hfT : IsProperMorphism (curvePlaceSpaceLevelModelMap k F S T f)) :
    (RingPoints.map f : CurvePlaceSpaceAdelePoints k F S X →
        CurvePlaceSpaceAdelePoints k F S Y) ⁻¹'
          Set.range (curvePlaceSpaceStageMap k F S Y T) =
      Set.range (curvePlaceSpaceStageMap k F S X T) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact AdelicSpacePreimageReduction.preimage_range_eq_of_equiv
    (curvePlaceSpaceStageEquiv k F S X T) (curvePlaceSpaceStageEquiv k F S Y T)
    (curvePlaceSpaceAdeleLevelBaseChangeEquiv k F S X T)
    (curvePlaceSpaceAdeleLevelBaseChangeEquiv k F S Y T)
    _ _ _ _ _ _
    (curvePlaceSpaceAdeleLevelBaseChangeEquiv_stageMap k F S X T)
    (curvePlaceSpaceAdeleLevelBaseChangeEquiv_stageMap k F S Y T)
    (curvePlaceSpaceAdeleLevelBaseChangeEquiv_map k F S T f)
    (curvePlaceSpaceFullLevelPreimage_of_valuative k F hv T.val
      (Finset.Nonempty.mono T.property hS) _ _ hX.baseChange hft.baseChange
      (curvePlaceSpaceLevelModelMap k F S T f) hfT)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- Full number-field adelic points commute with enlarging the integer base to `T`. -/
def numberFieldSpaceAdeleLevelBaseChangeEquiv
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (T : AdelicLevelIndexAbove S) :
    NumberFieldSpaceAdelePoints K S X ≃
      NumberFieldSpaceAdelePoints K T.val
        (numberFieldSpaceLevelBaseChange K T.property X) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) X).symm

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- Naturality of the full-adele base-change identification in a model morphism. -/
theorem numberFieldSpaceAdeleLevelBaseChangeEquiv_map (T : AdelicLevelIndexAbove S)
    (f : X ⟶ Y) (p : NumberFieldSpaceAdelePoints K S X) :
    numberFieldSpaceAdeleLevelBaseChangeEquiv K S Y T (RingPoints.map f p) =
      RingPoints.map (numberFieldSpaceLevelModelMap K S T f)
        (numberFieldSpaceAdeleLevelBaseChangeEquiv K S X T p) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) Y).symm
        (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K)) f)
      ((baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
        ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- The full and stage base-change identifications commute with the actual inclusion. -/
theorem numberFieldSpaceAdeleLevelBaseChangeEquiv_stageMap
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (T : AdelicLevelIndexAbove S)
    (p : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldSpaceAdeleLevelBaseChangeEquiv K S X T
        (numberFieldSpaceStageMap K S X T p) =
      RingPoints.changeRing (numberFieldSpaceLevelInclusion K T.val)
        (numberFieldSpaceStageEquiv K S X T p) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : numberFieldAdeleLevelOver K S T →ₐ[((T.val : Set (FinitePlace K)).integer K)]
      numberFieldAdeleOver K S :=
    { toRingHom := (numberFieldAdeleLevel K T.val).subtype, commutes' := fun _ => rfl }
  change (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) X).symm
        (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom p) =
    RingPoints.changeRing ψ
      ((baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
        ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_changeRing, Equiv.apply_symm_apply]
  rfl

/-- Exact preimages at every number-field stage, conditional on valuative existence and
properness of the base-changed morphism. All infinite factors are retained. -/
theorem numberFieldSpaceStagePreimage_of_valuative
    (hv : SpaceValuativeExistenceStatement.{u})
    (hX : IsSeparated X) (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (f : X ⟶ Y) (T : AdelicLevelIndexAbove S)
    (hfT : IsProperMorphism (numberFieldSpaceLevelModelMap K S T f)) :
    (RingPoints.map f : NumberFieldSpaceAdelePoints K S X →
        NumberFieldSpaceAdelePoints K S Y) ⁻¹'
          Set.range (numberFieldSpaceStageMap K S Y T) =
      Set.range (numberFieldSpaceStageMap K S X T) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact AdelicSpacePreimageReduction.preimage_range_eq_of_equiv
    (numberFieldSpaceStageEquiv K S X T) (numberFieldSpaceStageEquiv K S Y T)
    (numberFieldSpaceAdeleLevelBaseChangeEquiv K S X T)
    (numberFieldSpaceAdeleLevelBaseChangeEquiv K S Y T)
    _ _ _ _ _ _
    (numberFieldSpaceAdeleLevelBaseChangeEquiv_stageMap K S X T)
    (numberFieldSpaceAdeleLevelBaseChangeEquiv_stageMap K S Y T)
    (numberFieldSpaceAdeleLevelBaseChangeEquiv_map K S T f)
    (numberFieldSpaceFullLevelPreimage_of_valuative K hv T.val _ _
      hX.baseChange hft.baseChange (numberFieldSpaceLevelModelMap K S T f) hfT)

end NumberField

end Langlands.Global
