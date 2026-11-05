import Langlands.Global.AdelicLocalIntegralPreimageStatement

/-! # Integral preimages under actual proper model morphisms: proofs -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A universally closed morphism pulls integral-point ranges back to integral-point ranges. -/
theorem universallyClosed_ringPoint_preimage
    (C R L : Type u) [CommRing C] [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra C R] [Algebra R L] [Algebra C L] [IsScalarTower C R L]
    [IsFractionRing R L] (X Y : Over (Spec (CommRingCat.of C)))
    (f : X ⟶ Y) [UniversallyClosed f.left] :
    (fun p : RingPoint C X L => (p ≫ f : RingPoint C Y L)) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) (IsScalarTower.toAlgHom C R L)) =
      Set.range (RingPoint.changeRing (X := X) (IsScalarTower.toAlgHom C R L)) := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    have hcomm :
        z.left ≫ f.left = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ w.left :=
      congrArg (fun t : RingPoint C Y L => t.left) hw.symm
    have hVC : ValuativeCriterion.Existence f.left := by
      have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f.left := by
        rw [← UniversallyClosed.eq_valuativeCriterion]
        infer_instance
      exact h.1
    let sq : ValuativeCommSq f.left :=
      { R := R, K := L, i₁ := z.left, i₂ := w.left, commSq := ⟨hcomm⟩ }
    obtain ⟨l, hl₁, hl₂⟩ := (hVC sq).exists_lift
    let q : RingPoint C X R := Over.homMk l (by
      change l ≫ X.hom = (ringTest C R).hom
      rw [← Over.w f, ← Category.assoc, hl₂]
      exact Over.w w)
    exact ⟨q, RingPoint.ext C hl₁⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q ≫ f, (Category.assoc _ _ _).symm⟩

theorem valuationRingPointPreimage : ValuationRingPointPreimageStatement.{u} := by
  intro C R L _ _ _ _ _ _ _ _ _ _ X Y f _
  exact universallyClosed_ringPoint_preimage C R L X Y f

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

theorem curvePlaceLocalIntegralPreimage : CurvePlaceLocalIntegralPreimageStatement.{u} := by
  intro k F _ _ _ S v
  dsimp only
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S (.inr v)))
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v.1) :=
    ((algebraMap F (curvePlaceCompletion v.1)).comp
      (curvePlaceSIntegers k F S).subtype).toAlgebra
  let : IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) :=
    IsScalarTower.of_algebraMap_eq (R := curvePlaceSIntegers k F S)
      (S := curvePlaceCompletionIntegers v.1) (A := curvePlaceCompletion v.1) fun _ => rfl
  intro X Y f _
  exact universallyClosed_ringPoint_preimage (curvePlaceSIntegers k F S)
    (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) X Y f

theorem numberFieldLocalIntegralPreimage : NumberFieldLocalIntegralPreimageStatement.{u} := by
  intro K _ _ S v
  dsimp only
  let : Algebra ((S : Set (FinitePlace K)).integer K) (v.1.adicCompletionIntegers K) :=
    inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S (.inr (.inr v))))
  let : Algebra ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
    ((algebraMap K (FiniteCompletion K v.1)).comp
      ((S : Set (FinitePlace K)).integer K).subtype).toAlgebra
  let : SMul ((S : Set (FinitePlace K)).integer K) (FiniteCompletion K v.1) :=
    (inferInstance : Algebra ((S : Set (FinitePlace K)).integer K)
      (FiniteCompletion K v.1)).toSMul
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) :=
    IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace K)).integer K)
      (S := v.1.adicCompletionIntegers K) (A := FiniteCompletion K v.1) fun _ => rfl
  intro X Y f _
  exact universallyClosed_ringPoint_preimage ((S : Set (FinitePlace K)).integer K)
    (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) X Y f

/-- The exact generic and actual-arithmetic integral-preimage target. -/
theorem adelicLocalIntegralPreimage : AdelicLocalIntegralPreimageStatement.{u} :=
  ⟨valuationRingPointPreimage, curvePlaceLocalIntegralPreimage, numberFieldLocalIntegralPreimage⟩

end Langlands.Global
