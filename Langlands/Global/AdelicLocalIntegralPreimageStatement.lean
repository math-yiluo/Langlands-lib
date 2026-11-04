import Langlands.Global.AdelicLevelModelPoints
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Integral preimages under actual proper model morphisms -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The existence part of the valuative criterion, expressed on actual relative points. -/
def ValuationRingPointPreimageStatement : Prop :=
  ∀ (C R L : Type u) [CommRing C] [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra C R] [Algebra R L] [Algebra C L] [IsScalarTower C R L]
    [IsFractionRing R L] (X Y : Over (Spec (CommRingCat.of C)))
    (f : X ⟶ Y) [UniversallyClosed f.left],
    (fun p : RingPoint C X L => (p ≫ f : RingPoint C Y L)) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) (IsScalarTower.toAlgHom C R L)) =
      Set.range (RingPoint.changeRing (X := X) (IsScalarTower.toAlgHom C R L))

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The local integral-preimage assertion at every actual curve place outside a level. -/
def CurvePlaceLocalIntegralPreimageStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (v : {v : AlgebraicCurve.Place k F // v ∉ S}),
    letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
      inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S (.inr v)))
    letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) :=
      ((algebraMap F (curvePlaceCompletion v.1)).comp
        (curvePlaceSIntegers k F S).subtype).toAlgebra
    let ι : (curvePlaceCompletionIntegers v.1) →ₐ[curvePlaceSIntegers k F S]
        curvePlaceCompletion v.1 :=
      { toRingHom := algebraMap (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1),
        commutes' := fun _ => rfl }
    ∀ (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (f : X ⟶ Y) [IsProper f.left],
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceCompletion v.1) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceCompletion v.1))) ⁻¹'
          Set.range (RingPoint.changeRing (X := Y) ι) =
        Set.range (RingPoint.changeRing (X := X) ι)

/-- The local integral-preimage assertion at every finite number-field place outside a level. -/
def NumberFieldLocalIntegralPreimageStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (v : {v : FinitePlace K // v ∉ S}),
    letI : Algebra ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K) :=
      inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K S (.inr (.inr v))))
    letI : Algebra ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
      ((algebraMap K (FiniteCompletion K v.1)).comp
        ((S : Set (FinitePlace K)).integer K).subtype).toAlgebra
    let ι : (v.1.adicCompletionIntegers K) →ₐ[(S : Set (FinitePlace K)).integer K]
        FiniteCompletion K v.1 :=
      { toRingHom := algebraMap (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1),
        commutes' := fun _ => rfl }
    ∀ (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      (f : X ⟶ Y) [IsProper f.left],
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (FiniteCompletion K v.1) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y (FiniteCompletion K v.1))) ⁻¹'
          Set.range (RingPoint.changeRing (X := Y) ι) =
        Set.range (RingPoint.changeRing (X := X) ι)

/-- The generic valuative equality and its two actual arithmetic instances. -/
def AdelicLocalIntegralPreimageStatement : Prop :=
  ValuationRingPointPreimageStatement.{u} ∧
    CurvePlaceLocalIntegralPreimageStatement.{u} ∧
    NumberFieldLocalIntegralPreimageStatement.{u}

end Langlands.Global
