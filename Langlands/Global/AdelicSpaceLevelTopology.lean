import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.Global.AdelicLevelModelTransition

/-!
# Topology on adelic-level points of algebraic spaces

For an algebraic space `X` over the `S`-integers of a global field, the points with values
in the adelic level ring `A_{F,S}` are topologized through the coordinate map to the local
points: a point valued in a completion `F_v` carries the étale-chart topology of the base
change of `X` to `F_v`, and a point valued in a completed valuation ring `O_v` carries the
topology induced from the `F_v`-points. The module also defines the change of level along an
inclusion `S ⊆ T`, with values in the base change of `X` to the `T`-integers.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C] (X : AlgebraicSpace (Spec (CommRingCat.of C)))

section FieldValued

variable {A L : Type u} [CommRing A] [Algebra C A] [Field L] [Algebra C L]

/-- The map `X(A) → X_L(L)` along a `C`-algebra map `φ : A → L` to a field: change the
coefficients along `φ`, then view the `L`-point as a rational point of the base change of `X`
to `Spec L`. -/
def fieldValuedPointMap (φ : A →ₐ[C] L) :
    RingPoints C X A → RingPoints L (baseChange (Spec.algebraMap C L) X) L :=
  fun p => (baseChangeRingPointsEquiv C L L X).symm (RingPoints.changeRing φ p)

variable [TopologicalSpace L]

/-- The topology on `X(A)` induced along `fieldValuedPointMap` from the étale-chart topology
on the rational points of the base change of `X` to the topological field `L`. -/
@[instance_reducible]
def fieldValuedPointTopology (φ : A →ₐ[C] L) : TopologicalSpace (RingPoints C X A) :=
  TopologicalSpace.induced (fieldValuedPointMap C X φ)
    (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))

/-- The map to the rational points of the base change is inducing for this topology. -/
theorem fieldValuedPointMap_isInducing (φ : A →ₐ[C] L) :
    @IsInducing _ _ (fieldValuedPointTopology C X φ)
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (fieldValuedPointMap C X φ) :=
  @IsInducing.mk _ _ (fieldValuedPointTopology C X φ)
    (etaleChartTopology L (baseChange (Spec.algebraMap C L) X)) _ rfl

end FieldValued

section Coordinates

variable {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
variable [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
variable {A : Type u} [CommRing A] [Algebra C A]

/-- The coordinate map `X(A) → ∏ᵢ X(Rᵢ)` along a family of `C`-algebra maps `A → Rᵢ`. -/
def coordinatePointMap (π : ∀ i, A →ₐ[C] R i) : RingPoints C X A → ∀ i, RingPoints C X (R i) :=
  fun p i => RingPoints.changeRing (π i) p

/-- The product of the topologies `fieldValuedPointTopology C X (φ i)` on the factor points. -/
@[instance_reducible]
def coordinateProductTopology (φ : ∀ i, R i →ₐ[C] L i) :
    TopologicalSpace (∀ i, RingPoints C X (R i)) :=
  @Pi.topologicalSpace _ (fun i => RingPoints C X (R i))
    (fun i => fieldValuedPointTopology C X (φ i))

/-- The topology on `X(A)` induced along the coordinate map from the product of the
factor topologies. -/
@[instance_reducible]
def coordinatePointTopology (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i) :
    TopologicalSpace (RingPoints C X A) :=
  TopologicalSpace.induced (coordinatePointMap C X R π) (coordinateProductTopology C X R L φ)

/-- The coordinate map is inducing for this topology. -/
theorem coordinatePointMap_isInducing (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i) :
    @IsInducing _ _ (coordinatePointTopology C X R L φ π) (coordinateProductTopology C X R L φ)
      (coordinatePointMap C X R π) :=
  @IsInducing.mk _ _ (coordinatePointTopology C X R L φ π)
    (coordinateProductTopology C X R L φ) _ rfl

end Coordinates

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

/-- The completed field at each factor of a curve-place level: the factor itself at a place
in `S`, and the completion containing the completed valuation ring at a place outside `S`. -/
def CurvePlaceLevelField (S : Finset (AlgebraicCurve.Place k F)) :
    CurvePlaceLevelFactorIndex k F S → Type u
  | .inl v => curvePlaceCompletion v.1
  | .inr v => curvePlaceCompletion v.1

instance instAdelicSpaceLevelTopology1 (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) : Field (CurvePlaceLevelField k F S i) := by
  cases i <;> dsimp [CurvePlaceLevelField] <;> infer_instance

instance instAdelicSpaceLevelTopology2 (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace (CurvePlaceLevelField k F S i) := by
  cases i <;> dsimp [CurvePlaceLevelField] <;> infer_instance

/-- The identity at places in `S` and the inclusion of the completed valuation ring in the
completion at places outside `S`. -/
def curvePlaceLevelFieldInclusion (S : Finset (AlgebraicCurve.Place k F)) :
    (i : CurvePlaceLevelFactorIndex k F S) →
      CurvePlaceLevelFactor k F S i →+* CurvePlaceLevelField k F S i
  | .inl v => RingHom.id (curvePlaceCompletion v.1)
  | .inr v => (curvePlaceCompletionIntegers v.1).subtype

/-- The `S`-integers act on each completed field through the factor. -/
instance instAdelicSpaceLevelTopology3 (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S i) :=
  ((curvePlaceLevelFieldInclusion k F S i).comp
    (algebraMap (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i))).toAlgebra

/-- The inclusion of each factor in its completed field, as a map of `S`-integer algebras. -/
def curvePlaceLevelFieldAlgHom (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) :
    CurvePlaceLevelFactor k F S i →ₐ[curvePlaceSIntegers k F S] CurvePlaceLevelField k F S i :=
  { curvePlaceLevelFieldInclusion k F S i with commutes' := fun _ => rfl }

/-- The topology on the curve-place level points of an algebraic space over the
`S`-integers: induced along the coordinate projections from the product of the factor
topologies, where each factor carries the étale-chart topology through its completed field. -/
@[instance_reducible]
def curvePlaceSpaceLevelTopology (S : Finset (AlgebraicCurve.Place k F))
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    TopologicalSpace (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) :=
  coordinatePointTopology (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F S)
    (CurvePlaceLevelField k F S) (curvePlaceLevelFieldAlgHom k F S)
    (curvePlaceLevelFactorAlgHom k F S)

variable {k F} {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)

variable (k F) in
/-- The base change of an algebraic space along the inclusion of the `S`-integers in the
`T`-integers. -/
def curvePlaceSpaceLevelBaseChange
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F T))) :=
  baseChange (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST))) X

variable (k F) in
/-- The level inclusion as a morphism of test schemes over the `S`-integers, from the
spectrum of the `T`-level viewed over the `S`-integers. -/
def curvePlaceSpaceLevelTestMap :
    (Over.map (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST)))).obj
        (ringTest (curvePlaceSIntegers k F T) (curvePlaceAdeleLevel k F T)) ⟶
      ringTest (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelMap k F hST))) (by
    change Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelMap k F hST)) ≫
        Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelDiagonal k F S)) =
      Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelDiagonal k F T)) ≫
        Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (curvePlaceAdeleLevelDiagonal_natural k F hST))

variable (k F) in
/-- The change of level `X(A_{F,S}) → X_T(A_{F,T})`: pull a point back along the level
inclusion, as a point of the base change of `X` to the `T`-integers. -/
def curvePlaceSpaceLevelTransition
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) →
      RingPoints (curvePlaceSIntegers k F T) (curvePlaceSpaceLevelBaseChange k F hST X)
        (curvePlaceAdeleLevel k F T) :=
  X.pullback (curvePlaceSpaceLevelTestMap k F hST)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- The completed field at each factor of a number-field level: the factor itself at an
infinite place and at a finite place in `S`, and the completion containing the completed
integers at a finite place outside `S`. -/
def NumberFieldLevelField (S : Finset (FinitePlace K)) :
    NumberFieldLevelFactorIndex K S → Type u
  | .inl v => InfiniteCompletion K v
  | .inr (.inl v) => FiniteCompletion K v.1
  | .inr (.inr v) => FiniteCompletion K v.1

instance instAdelicSpaceLevelTopology4 (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) : Field (NumberFieldLevelField K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (Field (InfiniteCompletion K v))
  | inr j => cases j <;> dsimp [NumberFieldLevelField] <;> infer_instance

instance instAdelicSpaceLevelTopology5 (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace (NumberFieldLevelField K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (TopologicalSpace (InfiniteCompletion K v))
  | inr j => cases j <;> dsimp [NumberFieldLevelField] <;> infer_instance

/-- The identity at infinite places and at finite places in `S`, and the inclusion of the
completed integers in the completion at finite places outside `S`. -/
def numberFieldLevelFieldInclusion (S : Finset (FinitePlace K)) :
    (i : NumberFieldLevelFactorIndex K S) →
      NumberFieldLevelFactor K S i →+* NumberFieldLevelField K S i
  | .inl v => RingHom.id (InfiniteCompletion K v)
  | .inr (.inl v) => RingHom.id (FiniteCompletion K v.1)
  | .inr (.inr v) => (v.1.adicCompletionIntegers K).subtype

/-- The `S`-integers act on each completed field through the factor. -/
instance instAdelicSpaceLevelTopology6 (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K S i) :=
  ((numberFieldLevelFieldInclusion K S i).comp
    (algebraMap ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i))).toAlgebra

/-- The inclusion of each factor in its completed field, as a map of `S`-integer algebras. -/
def numberFieldLevelFieldAlgHom (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) :
    NumberFieldLevelFactor K S i →ₐ[(S : Set (FinitePlace K)).integer K]
      NumberFieldLevelField K S i :=
  { numberFieldLevelFieldInclusion K S i with commutes' := fun _ => rfl }

/-- The topology on the full number-field level points of an algebraic space over the
`S`-integers: induced along the coordinate projections from the product of the factor
topologies, where each factor carries the étale-chart topology through its completed field. -/
@[instance_reducible]
def numberFieldSpaceLevelTopology (S : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    TopologicalSpace
      (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) :=
  coordinatePointTopology ((S : Set (FinitePlace K)).integer K) X (NumberFieldLevelFactor K S)
    (NumberFieldLevelField K S) (numberFieldLevelFieldAlgHom K S)
    (numberFieldLevelFactorAlgHom K S)

variable {K} {S T : Finset (FinitePlace K)} (hST : S ⊆ T)

variable (K) in
/-- The base change of an algebraic space along the inclusion of the `S`-integers in the
`T`-integers. -/
def numberFieldSpaceLevelBaseChange
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    AlgebraicSpace (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K))) :=
  baseChange (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST))) X

variable (K) in
/-- The level inclusion as a morphism of test schemes over the `S`-integers, from the
spectrum of the `T`-level viewed over the `S`-integers. -/
def numberFieldSpaceLevelTestMap :
    (Over.map (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST)))).obj
        (ringTest ((T : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T)) ⟶
      ringTest ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelMap K hST))) (by
    change Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelMap K hST)) ≫
        Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelDiagonal K S)) =
      Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelDiagonal K T)) ≫
        Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (numberFieldAdeleLevelDiagonal_natural K hST))

variable (K) in
/-- The change of level `X(A_{F,S}) → X_T(A_{F,T})`: pull a point back along the level
inclusion, as a point of the base change of `X` to the `T`-integers. -/
def numberFieldSpaceLevelTransition
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) →
      RingPoints ((T : Set (FinitePlace K)).integer K) (numberFieldSpaceLevelBaseChange K hST X)
        (numberFieldAdeleLevel K T) :=
  X.pullback (numberFieldSpaceLevelTestMap K hST)

end NumberField

end Langlands.Global
