import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.CompleteProof

/-!
# Adelic-level points of separated finite type algebraic spaces

Proof of Conrad's Proposition 5.2 for global fields of both characteristics: the points of a
separated algebraic space of finite type over the `S`-integers with values in the adelic level
ring are the families of local points. The level ring is the product of the completions at the
places of `S` (and the infinite places) and the completed valuation rings away from `S`; each
factor is a complete local ring, so `SpaceProductPoints.separatedProductPoints_bijective` applies.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry IsDedekindDomain
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTestMap ringTestMap_id)

namespace Langlands.Global

namespace AdelicSpaceLevelPointsProof

/-- A field is complete for its maximal ideal, which is zero. -/
theorem isAdicComplete_field (K : Type u) [Field K] :
    IsAdicComplete (IsLocalRing.maximalIdeal K) K := by
  rw [IsLocalRing.maximalIdeal_eq_bot]
  infer_instance

/-- The completed integers at a height-one prime are complete for their maximal ideal. -/
theorem isAdicComplete_adicCompletionIntegers (A : Type u) [CommRing A] [IsDedekindDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] (v : HeightOneSpectrum A) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete
    (K := v.adicCompletion K) (Gamma := WithZero (Multiplicative ℤ))

/-- Change of coefficients along an isomorphism is bijective. -/
theorem changeRing_bijective {C : Type u} [CommRing C]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (e : A ≃ₐ[C] B) :
    Function.Bijective (RingPoints.changeRing (X := X) e.toAlgHom) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨RingPoints.changeRing e.symm.toAlgHom, ?_, ?_⟩
  · intro x
    rw [ProductPointsDescent.changeRing_changeRing]
    have : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id C A := AlgHom.ext fun a => e.symm_apply_apply a
    rw [this]
    change X.pullback (ringTestMap C (AlgHom.id C A)) x = x
    rw [ringTestMap_id]
    exact pullback_id X _ x
  · intro x
    rw [ProductPointsDescent.changeRing_changeRing]
    have : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id C B := AlgHom.ext fun a => e.apply_symm_apply a
    rw [this]
    change X.pullback (ringTestMap C (AlgHom.id C B)) x = x
    rw [ringTestMap_id]
    exact pullback_id X _ x

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

instance (i : NumberFieldLevelFactorIndex K S) :
    IsAdicComplete (IsLocalRing.maximalIdeal (NumberFieldLevelFactor K S i))
      (NumberFieldLevelFactor K S i) := by
  rcases i with v | v | v
  · exact isAdicComplete_field (InfiniteCompletion K v)
  · exact isAdicComplete_field (FiniteCompletion K v.1)
  · exact isAdicComplete_adicCompletionIntegers (NumberField.RingOfIntegers K) K v.1

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] (S : Finset (AlgebraicCurve.Place k F))

instance (i : CurvePlaceLevelFactorIndex k F S) :
    IsAdicComplete (IsLocalRing.maximalIdeal (CurvePlaceLevelFactor k F S i))
      (CurvePlaceLevelFactor k F S i) := by
  rcases i with v | v
  · exact isAdicComplete_field (curvePlaceCompletion v.1)
  · exact isAdicComplete_adicCompletionIntegers _ F v.1.heightOneSpectrum

end Curve

end AdelicSpaceLevelPointsProof

open AdelicSpaceLevelPointsProof SpaceProductPoints in
/-- **Conrad's Proposition 5.2, number fields.** -/
theorem numberFieldSpaceLevelPoints : NumberFieldSpaceLevelPointsStatement.{u} := by
  intro K _ _ S X hX hft
  have hcomp : (fun (p : RingPoints ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S)) (i : NumberFieldLevelFactorIndex K S) =>
        RingPoints.changeRing (numberFieldLevelFactorAlgHom K S i) p) =
      (fun q i => RingPoints.changeRing (Pi.evalAlgHom _ (NumberFieldLevelFactor K S) i) q) ∘
        RingPoints.changeRing (numberFieldLevelFactorAlgEquiv K S).toAlgHom := by
    funext p i
    simp only [Function.comp_apply, ProductPointsDescent.changeRing_changeRing]
    rfl
  rw [hcomp]
  exact (separatedProductPoints_bijective hX hft _ (NumberFieldLevelFactor K S)).comp
    (changeRing_bijective _)

open AdelicSpaceLevelPointsProof SpaceProductPoints in
/-- **Conrad's Proposition 5.2, global function fields.** -/
theorem curvePlaceSpaceLevelPoints : CurvePlaceSpaceLevelPointsStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S _ X hX hft
  have hcomp : (fun (p : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (i : CurvePlaceLevelFactorIndex k F S) =>
        RingPoints.changeRing (curvePlaceLevelFactorAlgHom k F S i) p) =
      (fun q i => RingPoints.changeRing (Pi.evalAlgHom _ (CurvePlaceLevelFactor k F S) i) q) ∘
        RingPoints.changeRing (curvePlaceLevelFactorAlgEquiv k F S).toAlgHom := by
    funext p i
    simp only [Function.comp_apply, ProductPointsDescent.changeRing_changeRing]
    rfl
  rw [hcomp]
  exact (separatedProductPoints_bijective hX hft _ (CurvePlaceLevelFactor k F S)).comp
    (changeRing_bijective _)

/-- **Conrad's Proposition 5.2** (printed pp.13–14), for global fields of both
characteristics. -/
theorem adelicSpaceLevelPoints : AdelicSpaceLevelPointsStatement.{u} :=
  ⟨numberFieldSpaceLevelPoints, curvePlaceSpaceLevelPoints⟩

end Langlands.Global
