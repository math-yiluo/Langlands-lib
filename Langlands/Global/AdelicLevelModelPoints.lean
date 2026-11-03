import Langlands.Global.NumberFieldAdeleLevel
import Langlands.Global.CurvePlaceAdeleRing
import Langlands.AlgebraicGeometry.PointTopology.LocalProductPoints

/-! # Actual local-model points at an adelic level -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C]

/-- An equivalence of coefficient algebras acts on actual relative scheme points. -/
def ringPointChangeRingEquiv (X : Over (Spec (CommRingCat.of C)))
    {A B : Type u} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
    (e : A ≃ₐ[C] B) : RingPoint C X A ≃ RingPoint C X B where
  toFun := RingPoint.changeRing e.toAlgHom
  invFun := RingPoint.changeRing e.symm.toAlgHom
  left_inv p := by
    let p₀ : ringTest C A ⟶ X := p
    change ringTestMap C e.symm.toAlgHom ≫ (ringTestMap C e.toAlgHom ≫ p₀) = p₀
    rw [← Category.assoc, ← ringTestMap_comp]
    have h : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id C A := by ext; simp
    rw [h, ringTestMap_id, Category.id_comp]
  right_inv p := by
    let p₀ : ringTest C B ⟶ X := p
    change ringTestMap C e.toAlgHom ≫ (ringTestMap C e.symm.toAlgHom ≫ p₀) = p₀
    rw [← Category.assoc, ← ringTestMap_comp]
    have h : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id C B := by ext; simp
    rw [h, ringTestMap_id, Category.id_comp]

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

/-- The two sorts of actual local factors of a curve-place adelic level. -/
abbrev CurvePlaceLevelFactorIndex (S : Finset (AlgebraicCurve.Place k F)) :=
  {v : AlgebraicCurve.Place k F // v ∈ S} ⊕
    {v : AlgebraicCurve.Place k F // v ∉ S}

/-- Completed fields in `S` and completed valuation rings outside `S`. -/
def CurvePlaceLevelFactor (S : Finset (AlgebraicCurve.Place k F)) :
    CurvePlaceLevelFactorIndex k F S → Type u
  | .inl v => curvePlaceCompletion v.1
  | .inr v => curvePlaceCompletionIntegers v.1

instance instAdelicLevelModelPoints1 (S : Finset (AlgebraicCurve.Place k F)) (i : CurvePlaceLevelFactorIndex k F S) :
    CommRing (CurvePlaceLevelFactor k F S i) := by cases i <;> dsimp [CurvePlaceLevelFactor] <;> infer_instance

instance instAdelicLevelModelPoints2 (S : Finset (AlgebraicCurve.Place k F)) (i : CurvePlaceLevelFactorIndex k F S) :
    TopologicalSpace (CurvePlaceLevelFactor k F S i) := by
  cases i <;> dsimp [CurvePlaceLevelFactor] <;> infer_instance

instance instAdelicLevelModelPoints3 (S : Finset (AlgebraicCurve.Place k F)) (i : CurvePlaceLevelFactorIndex k F S) :
    IsTopologicalRing (CurvePlaceLevelFactor k F S i) := by
  cases i with
  | inl v => exact inferInstanceAs (IsTopologicalRing (curvePlaceCompletion v.1))
  | inr v => exact Subring.instIsTopologicalRing (curvePlaceCompletionIntegers v.1).toSubring

instance instAdelicLevelModelPoints4 (S : Finset (AlgebraicCurve.Place k F)) (i : CurvePlaceLevelFactorIndex k F S) :
    IsLocalRing (CurvePlaceLevelFactor k F S i) := by
  cases i <;> dsimp [CurvePlaceLevelFactor] <;> infer_instance

/-- The published level product equivalence, indexed as one dependent product. -/
def curvePlaceLevelFactorRingEquiv (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceAdeleLevel k F S ≃+* ∀ i, CurvePlaceLevelFactor k F S i where
  toEquiv := (curvePlaceAdeleLevelProductEquiv k F S).toEquiv.trans
    (Equiv.sumPiEquivProdPi (CurvePlaceLevelFactor k F S)).symm
  map_mul' a b := by funext i; cases i <;> rfl
  map_add' a b := by funext i; cases i <;> rfl

/-- The literal projection of the level ring to an actual local factor. -/
def curvePlaceLevelFactorProjection (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) :
    curvePlaceAdeleLevel k F S →+* CurvePlaceLevelFactor k F S i :=
  (Pi.evalRingHom _ i).comp (curvePlaceLevelFactorRingEquiv k F S).toRingHom

/-- The original outside-`S` integer diagonal supplies each local scalar action. -/
instance instAdelicLevelModelPoints5 (S : Finset (AlgebraicCurve.Place k F)) (i : CurvePlaceLevelFactorIndex k F S) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) :=
  ((curvePlaceLevelFactorProjection k F S i).comp
    (curvePlaceAdeleLevelDiagonal k F S)).toAlgebra

/-- The actual ring comparison respects these original scalar actions. -/
def curvePlaceLevelFactorAlgEquiv (S : Finset (AlgebraicCurve.Place k F)) :
    curvePlaceAdeleLevel k F S ≃ₐ[curvePlaceSIntegers k F S]
      ∀ i, CurvePlaceLevelFactor k F S i :=
  { curvePlaceLevelFactorRingEquiv k F S with commutes' := fun _ => rfl }

/-- Coordinate projection as a morphism of the original model's scalar algebras. -/
def curvePlaceLevelFactorAlgHom (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) :
    curvePlaceAdeleLevel k F S →ₐ[curvePlaceSIntegers k F S] CurvePlaceLevelFactor k F S i :=
  { curvePlaceLevelFactorProjection k F S i with commutes' := fun _ => rfl }

@[simp]
theorem curvePlaceLevelFactorProjection_field (S : Finset (AlgebraicCurve.Place k F))
    (a : curvePlaceAdeleLevel k F S) (v : {v : AlgebraicCurve.Place k F // v ∈ S}) :
    curvePlaceLevelFactorProjection k F S (.inl v) a =
      (a : CurvePlaceAdeleRing k F) v.1 := rfl

@[simp]
theorem curvePlaceLevelFactorProjection_integer (S : Finset (AlgebraicCurve.Place k F))
    (a : curvePlaceAdeleLevel k F S) (v : {v : AlgebraicCurve.Place k F // v ∉ S}) :
    ((show curvePlaceCompletionIntegers v.1 from
      curvePlaceLevelFactorProjection k F S (.inr v) a) : curvePlaceCompletion v.1) =
      (a : CurvePlaceAdeleRing k F) v.1 := rfl

@[simp]
theorem curvePlaceLevelFactor_algebraMap_field (S : Finset (AlgebraicCurve.Place k F))
    (c : curvePlaceSIntegers k F S) (v : {v : AlgebraicCurve.Place k F // v ∈ S}) :
    algebraMap (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S (.inl v)) c =
      algebraMap F (curvePlaceCompletion v.1) c.val := rfl

@[simp]
theorem curvePlaceLevelFactor_algebraMap_integer (S : Finset (AlgebraicCurve.Place k F))
    (c : curvePlaceSIntegers k F S) (v : {v : AlgebraicCurve.Place k F // v ∉ S}) :
    ((show curvePlaceCompletionIntegers v.1 from
      algebraMap (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S (.inr v)) c) : curvePlaceCompletion v.1) =
      algebraMap F (curvePlaceCompletion v.1) c.val := rfl

/-- Actual level-valued model points mapped to points of the actual local base changes. -/
def curvePlaceLevelModelPointMap (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) →
      ∀ i, RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
        (CurvePlaceLevelFactor k F S i) :=
  fun p i => ringPointBaseChangeEquiv _ _ _ X
    (p.changeRing (curvePlaceLevelFactorAlgHom k F S i))

/-- This is the generic actual local-model comparison after the explicit level equivalence. -/
theorem curvePlaceLevelModelPointMap_eq (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    curvePlaceLevelModelPointMap k F S X =
      localProductPointMap (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S) X ∘
        ringPointChangeRingEquiv (curvePlaceSIntegers k F S) X
          (curvePlaceLevelFactorAlgEquiv k F S) := by
  funext p i
  change ringPointBaseChangeEquiv _ _ _ X _ = ringPointBaseChangeEquiv _ _ _ X _
  congr 1
  let p₀ : ringTest (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S) ⟶ X := p
  change ringTestMap _ (curvePlaceLevelFactorAlgHom k F S i) ≫ p₀ =
    ringTestMap _ (Pi.evalAlgHom _ _ i) ≫
      (ringTestMap _ (curvePlaceLevelFactorAlgEquiv k F S).toAlgHom ≫ p₀)
  rw [← Category.assoc, ← ringTestMap_comp]
  rfl

/-- The local point projects to exactly the coordinate restriction of the original point. -/
@[simp]
theorem curvePlaceLevelModelPointMap_left_fst (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
    (i : CurvePlaceLevelFactorIndex k F S) :
    (curvePlaceLevelModelPointMap k F S X p i).left ≫
      pullback.fst X.hom (Spec.algebraMap _ (CurvePlaceLevelFactor k F S i)) =
        Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorProjection k F S i)) ≫ p.left :=
  ringPointBaseChangeEquiv_left_fst _ _ _ X _

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Every infinite place, finite places in `S`, and finite places outside `S`. -/
abbrev NumberFieldLevelFactorIndex (S : Finset (FinitePlace K)) :=
  InfinitePlace K ⊕ ({v : FinitePlace K // v ∈ S} ⊕ {v : FinitePlace K // v ∉ S})

/-- Actual infinite and finite completions, and completed integers away from `S`. -/
def NumberFieldLevelFactor (S : Finset (FinitePlace K)) :
    NumberFieldLevelFactorIndex K S → Type u
  | .inl v => InfiniteCompletion K v
  | .inr (.inl v) => FiniteCompletion K v.1
  | .inr (.inr v) => v.1.adicCompletionIntegers K

instance instAdelicLevelModelPoints6 (S : Finset (FinitePlace K)) (i : NumberFieldLevelFactorIndex K S) :
    CommRing (NumberFieldLevelFactor K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (CommRing (InfiniteCompletion K v))
  | inr j => cases j <;> dsimp [NumberFieldLevelFactor] <;> infer_instance

instance instAdelicLevelModelPoints7 (S : Finset (FinitePlace K)) (i : NumberFieldLevelFactorIndex K S) :
    TopologicalSpace (NumberFieldLevelFactor K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (TopologicalSpace (InfiniteCompletion K v))
  | inr j => cases j <;> dsimp [NumberFieldLevelFactor] <;> infer_instance

instance instAdelicLevelModelPoints8 (S : Finset (FinitePlace K)) (i : NumberFieldLevelFactorIndex K S) :
    IsTopologicalRing (NumberFieldLevelFactor K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (IsTopologicalRing (InfiniteCompletion K v))
  | inr j =>
    cases j with
    | inl v => exact inferInstanceAs (IsTopologicalRing (FiniteCompletion K v.1))
    | inr v => exact Subring.instIsTopologicalRing (v.1.adicCompletionIntegers K).toSubring

instance instAdelicLevelModelPoints9 (S : Finset (FinitePlace K)) (i : NumberFieldLevelFactorIndex K S) :
    IsLocalRing (NumberFieldLevelFactor K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (IsLocalRing (InfiniteCompletion K v))
  | inr j => cases j <;> dsimp [NumberFieldLevelFactor] <;> infer_instance

/-- The published full adelic level product, expressed as a single dependent product. -/
def numberFieldLevelFactorRingEquiv (S : Finset (FinitePlace K)) :
    numberFieldAdeleLevel K S ≃+* ∀ i, NumberFieldLevelFactor K S i where
  toEquiv := (numberFieldAdeleLevelProductEquiv K S).toEquiv.trans
    ((Equiv.sumPiEquivProdPi (NumberFieldLevelFactor K S)).trans
      ((Equiv.refl (InfiniteAdeles K)).prodCongr
        (Equiv.sumPiEquivProdPi (fun j => NumberFieldLevelFactor K S (.inr j))))).symm
  map_mul' a b := by funext i; cases i with
    | inl v => rfl
    | inr j => cases j <;> rfl
  map_add' a b := by funext i; cases i with
    | inl v => rfl
    | inr j => cases j <;> rfl

/-- The actual projection from a full level to one of its completed factors. -/
def numberFieldLevelFactorProjection (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) :
    numberFieldAdeleLevel K S →+* NumberFieldLevelFactor K S i :=
  (Pi.evalRingHom _ i).comp (numberFieldLevelFactorRingEquiv K S).toRingHom

/-- Each scalar action is induced by the actual number-field S-integer diagonal. -/
instance instAdelicLevelModelPoints10 (S : Finset (FinitePlace K)) (i : NumberFieldLevelFactorIndex K S) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) :=
  ((numberFieldLevelFactorProjection K S i).comp
    (numberFieldAdeleLevelDiagonal K S)).toAlgebra

/-- The full level product isomorphism respects the actual S-integer actions. -/
def numberFieldLevelFactorAlgEquiv (S : Finset (FinitePlace K)) :
    numberFieldAdeleLevel K S ≃ₐ[(S : Set (FinitePlace K)).integer K]
      ∀ i, NumberFieldLevelFactor K S i :=
  { numberFieldLevelFactorRingEquiv K S with commutes' := fun _ => rfl }

/-- The coordinate projection as a map of the original model's scalar algebras. -/
def numberFieldLevelFactorAlgHom (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) :
    numberFieldAdeleLevel K S →ₐ[(S : Set (FinitePlace K)).integer K]
      NumberFieldLevelFactor K S i :=
  { numberFieldLevelFactorProjection K S i with commutes' := fun _ => rfl }

@[simp]
theorem numberFieldLevelFactorProjection_infinite (S : Finset (FinitePlace K))
    (a : numberFieldAdeleLevel K S) (v : InfinitePlace K) :
    numberFieldLevelFactorProjection K S (.inl v) a =
      infiniteProjection K v (a : Adeles K) := rfl

@[simp]
theorem numberFieldLevelFactorProjection_finite (S : Finset (FinitePlace K))
    (a : numberFieldAdeleLevel K S) (v : {v : FinitePlace K // v ∈ S}) :
    numberFieldLevelFactorProjection K S (.inr (.inl v)) a =
      finiteProjection K v.1 (a : Adeles K) := rfl

@[simp]
theorem numberFieldLevelFactorProjection_integer (S : Finset (FinitePlace K))
    (a : numberFieldAdeleLevel K S) (v : {v : FinitePlace K // v ∉ S}) :
    ((show v.1.adicCompletionIntegers K from
      numberFieldLevelFactorProjection K S (.inr (.inr v)) a) : FiniteCompletion K v.1) =
      finiteProjection K v.1 (a : Adeles K) := rfl

@[simp]
theorem numberFieldLevelFactor_algebraMap_infinite (S : Finset (FinitePlace K))
    (c : (S : Set (FinitePlace K)).integer K) (v : InfinitePlace K) :
    algebraMap ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S (.inl v)) c =
        algebraMap K (InfiniteCompletion K v) c.val := rfl

@[simp]
theorem numberFieldLevelFactor_algebraMap_finite (S : Finset (FinitePlace K))
    (c : (S : Set (FinitePlace K)).integer K) (v : {v : FinitePlace K // v ∈ S}) :
    algebraMap ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S (.inr (.inl v))) c =
        algebraMap K (FiniteCompletion K v.1) c.val := rfl

@[simp]
theorem numberFieldLevelFactor_algebraMap_integer (S : Finset (FinitePlace K))
    (c : (S : Set (FinitePlace K)).integer K) (v : {v : FinitePlace K // v ∉ S}) :
    ((show v.1.adicCompletionIntegers K from
      algebraMap ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K S (.inr (.inr v))) c) : FiniteCompletion K v.1) =
      algebraMap K (FiniteCompletion K v.1) c.val := rfl

/-- Actual full-level model points restricted to the actual local base changes. -/
def numberFieldLevelModelPointMap (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) →
      ∀ i, RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
        (NumberFieldLevelFactor K S i) :=
  fun p i => ringPointBaseChangeEquiv _ _ _ X
    (p.changeRing (numberFieldLevelFactorAlgHom K S i))

/-- The full-level map is the generic actual local-model map after explicit coefficient transport. -/
theorem numberFieldLevelModelPointMap_eq (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    numberFieldLevelModelPointMap K S X =
      localProductPointMap ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S) X ∘
        ringPointChangeRingEquiv ((S : Set (FinitePlace K)).integer K) X
          (numberFieldLevelFactorAlgEquiv K S) := by
  funext p i
  change ringPointBaseChangeEquiv _ _ _ X _ = ringPointBaseChangeEquiv _ _ _ X _
  congr 1
  let p₀ : ringTest ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S) ⟶ X := p
  change ringTestMap _ (numberFieldLevelFactorAlgHom K S i) ≫ p₀ =
    ringTestMap _ (Pi.evalAlgHom _ _ i) ≫
      (ringTestMap _ (numberFieldLevelFactorAlgEquiv K S).toAlgHom ≫ p₀)
  rw [← Category.assoc, ← ringTestMap_comp]
  rfl

/-- Projection to the original model is the actual coordinate restriction. -/
@[simp]
theorem numberFieldLevelModelPointMap_left_fst (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
    (i : NumberFieldLevelFactorIndex K S) :
    (numberFieldLevelModelPointMap K S X p i).left ≫
      pullback.fst X.hom (Spec.algebraMap _ (NumberFieldLevelFactor K S i)) =
        Spec.map (CommRingCat.ofHom (numberFieldLevelFactorProjection K S i)) ≫ p.left :=
  ringPointBaseChangeEquiv_left_fst _ _ _ X _

end NumberField

end Langlands.Global
