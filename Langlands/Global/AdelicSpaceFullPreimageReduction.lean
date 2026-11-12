import Langlands.Global.AdelicSpacePreimageAssembly
import Langlands.Global.AdelicSpacePointTopology

/-! # Arithmetic full-level preimages for algebraic-space morphisms -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.AdelicSpacePreimageAssembly

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

/-- The level ring included in the full adele ring, over the integer-ring base. -/
def curvePlaceSpaceLevelInclusion (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceAdeleLevel k F S →ₐ[curvePlaceSIntegers k F S] curvePlaceAdeleOver k F S :=
  { toRingHom := (curvePlaceAdeleLevel k F S).subtype, commutes' := fun _ => rfl }

/-- All completed-field coordinates of the curve-place adele ring. -/
def curvePlaceSpaceFullProductMap (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceAdeleOver k F S →ₐ[curvePlaceSIntegers k F S]
      ∀ i, CurvePlaceLevelField k F S i :=
  { toRingHom := RingHom.pi (fun i => match i with
      | .inl v => RestrictedProduct.evalRingHom (fun w => curvePlaceCompletion w) v.1
      | .inr v => RestrictedProduct.evalRingHom (fun w => curvePlaceCompletion w) v.1)
    commutes' := by intro c; funext i; cases i <;> rfl }

/-- The full completed-field coordinates distinguish adeles. -/
theorem curvePlaceSpaceFullProductMap_injective (S : Finset (AlgebraicCurve.Place k F)) :
    Function.Injective (curvePlaceSpaceFullProductMap k F S) := by
  classical
  intro a b h
  apply RestrictedProduct.ext
  intro v
  by_cases hv : v ∈ S
  · exact congrFun h (.inl ⟨v, hv⟩)
  · exact congrFun h (.inr ⟨v, hv⟩)

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F]

/-- Exact curve-place level preimages, conditional on the valuative-existence input. -/
theorem curvePlaceSpaceFullLevelPreimage_of_valuative
    (hv : SpaceValuativeExistenceStatement.{u})
    (S : Finset (AlgebraicCurve.Place k F)) (hS : S.Nonempty)
    (X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (f : X ⟶ Y) (hf : IsProperMorphism f) :
    (RingPoints.map f : CurvePlaceSpaceAdelePoints k F S X →
        CurvePlaceSpaceAdelePoints k F S Y) ⁻¹'
        Set.range (RingPoints.changeRing (X := Y) (curvePlaceSpaceLevelInclusion k F S)) =
      Set.range (RingPoints.changeRing (X := X) (curvePlaceSpaceLevelInclusion k F S)) := by
  refine preimage_eq_of_local_preimages (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevel k F S) (curvePlaceAdeleOver k F S)
    (CurvePlaceLevelFactor k F S) (CurvePlaceLevelField k F S)
    _ (curvePlaceLevelFactorAlgHom k F S) (curvePlaceSpaceFullProductMap k F S)
    (curvePlaceSpaceFullProductMap_injective k F S) (curvePlaceLevelFieldAlgHom k F S)
    ?_ X Y f hX (curvePlaceSpaceLevelPoints k F S hS X hX hft).2 ?_
  · intro i
    ext a
    cases i <;> rfl
  · intro i
    cases i with
    | inl v =>
      exact preimage_eq_of_bijective (curvePlaceLevelFieldAlgHom k F S (.inl v))
        Function.bijective_id X Y f
    | inr v =>
      let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
        inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F S (.inr v)))
      let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) :=
        inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
          (CurvePlaceLevelField k F S (.inr v)))
      let : IsScalarTower (curvePlaceSIntegers k F S)
          (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) :=
        IsScalarTower.of_algebraMap_eq (R := curvePlaceSIntegers k F S)
          (S := curvePlaceCompletionIntegers v.1) (A := curvePlaceCompletion v.1)
          fun _ => rfl
      exact integral_preimage_of_valuative hv (curvePlaceSIntegers k F S)
        (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) X Y f hf

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- The level ring included in the full adele ring, over the integer-ring base. -/
def numberFieldSpaceLevelInclusion (S : Finset (FinitePlace K)) :
    numberFieldAdeleLevel K S →ₐ[(S : Set (FinitePlace K)).integer K] numberFieldAdeleOver K S :=
  { toRingHom := (numberFieldAdeleLevel K S).subtype, commutes' := fun _ => rfl }

/-- All completed-field coordinates of the number-field adele ring, including infinite places. -/
def numberFieldSpaceFullProductMap (S : Finset (FinitePlace K)) :
    numberFieldAdeleOver K S →ₐ[(S : Set (FinitePlace K)).integer K]
      ∀ i, NumberFieldLevelField K S i :=
  { toRingHom := RingHom.pi (fun i => match i with
      | .inl v => infiniteProjection K v
      | .inr (.inl v) => finiteProjection K v.1
      | .inr (.inr v) => finiteProjection K v.1)
    commutes' := by
      intro c
      funext i
      cases i with
      | inl v => rfl
      | inr j => cases j <;> rfl }

/-- The full completed-field coordinates distinguish adeles. -/
theorem numberFieldSpaceFullProductMap_injective (S : Finset (FinitePlace K)) :
    Function.Injective (numberFieldSpaceFullProductMap K S) := by
  classical
  intro a b h
  apply Prod.ext
  · funext v
    exact congrFun h (.inl v)
  · apply RestrictedProduct.ext
    intro v
    by_cases hv : v ∈ S
    · exact congrFun h (.inr (.inl ⟨v, hv⟩))
    · exact congrFun h (.inr (.inr ⟨v, hv⟩))

/-- Exact number-field level preimages, conditional on the valuative-existence input. -/
theorem numberFieldSpaceFullLevelPreimage_of_valuative
    (hv : SpaceValuativeExistenceStatement.{u}) (S : Finset (FinitePlace K))
    (X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (hX : IsSeparated X) (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (f : X ⟶ Y) (hf : IsProperMorphism f) :
    (RingPoints.map f : NumberFieldSpaceAdelePoints K S X →
        NumberFieldSpaceAdelePoints K S Y) ⁻¹'
        Set.range (RingPoints.changeRing (X := Y) (numberFieldSpaceLevelInclusion K S)) =
      Set.range (RingPoints.changeRing (X := X) (numberFieldSpaceLevelInclusion K S)) := by
  refine preimage_eq_of_local_preimages ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevel K S) (numberFieldAdeleOver K S)
    (NumberFieldLevelFactor K S) (NumberFieldLevelField K S)
    _ (numberFieldLevelFactorAlgHom K S) (numberFieldSpaceFullProductMap K S)
    (numberFieldSpaceFullProductMap_injective K S) (numberFieldLevelFieldAlgHom K S)
    ?_ X Y f hX (numberFieldSpaceLevelPoints K S X hX hft).2 ?_
  · intro i
    ext a
    cases i with
    | inl v => rfl
    | inr j => cases j <;> rfl
  · intro i
    cases i with
    | inl v =>
      exact preimage_eq_of_bijective (numberFieldLevelFieldAlgHom K S (.inl v))
        Function.bijective_id X Y f
    | inr j =>
      cases j with
      | inl v =>
        exact preimage_eq_of_bijective (numberFieldLevelFieldAlgHom K S (.inr (.inl v)))
          Function.bijective_id X Y f
      | inr v =>
        let : Algebra ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K) :=
          inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
            (NumberFieldLevelFactor K S (.inr (.inr v))))
        let : Algebra ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
          inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
            (NumberFieldLevelField K S (.inr (.inr v))))
        let : SMul ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
          (inferInstance : Algebra ((S : Set (FinitePlace K)).integer K)
            (FiniteCompletion K v.1)).toSMul
        let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
            (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) :=
          IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace K)).integer K)
            (S := v.1.adicCompletionIntegers K) (A := FiniteCompletion K v.1)
            fun _ => rfl
        exact integral_preimage_of_valuative hv ((S : Set (FinitePlace K)).integer K)
          (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) X Y f hf

end NumberField

end Langlands.Global
