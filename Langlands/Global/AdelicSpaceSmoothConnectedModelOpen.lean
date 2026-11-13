import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionUniformLifts
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteFieldSmoothPointOpenProof
import Langlands.Global.AdelicSpaceIntegerBase
import Langlands.Global.AdelicSpaceResidueComponentSurjectivity
import Langlands.Global.AdelicSpaceSmoothLocalOpenReduction

/-! # Smooth connected model openness without a fixed dimension -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberField

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  [Algebra (ULift.{u} ℤ) (curvePlaceSIntegers k F S)]
  [LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) (curvePlaceSIntegers k F S))]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- A uniform bound with varying dimension gives almost-all actual factor surjectivity. -/
theorem curvePlaceSmoothConnectedFactor_eventually_surjective
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := CurvePlaceLevelFactor k F S i) f) := by
  classical
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  obtain ⟨c, _, hs⟩ := SmoothDimensionUniformLifts.exists_uniform_henselian_surjectivity
    (curvePlaceSIntegers k F S) hLW X Y f hX hXft hY hYft hf hconn
  let small : Set {v : AlgebraicCurve.Place k F // v ∉ S} :=
    {v | (Nat.card (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v.1)) : ℝ) ≤ c ^ 2}
  have hsmall : small.Finite :=
    (curvePlaceCompletion_finite_small_residue k F (c ^ 2)).preimage
      Subtype.val_injective.injOn
  apply Filter.eventually_cofinite.mpr
  apply ((Set.finite_range
    (Sum.inl : {v : AlgebraicCurve.Place k F // v ∈ S} →
      CurvePlaceLevelFactorIndex k F S)).union (hsmall.image Sum.inr)).subset
  intro i hi
  rcases i with v | v
  · exact Or.inl ⟨v, rfl⟩
  · apply Or.inr
    refine ⟨v, ?_, rfl⟩
    by_contra hv
    have hlarge : c ^ 2 < (Nat.card (IsLocalRing.ResidueField
        (CurvePlaceLevelFactor k F S (.inr v))) : ℝ) := lt_of_not_ge hv
    let O := CurvePlaceLevelFactor k F S (.inr v)
    let : HenselianLocalRing O := curvePlaceCompletionIntegers_henselian v.1
    let : Module.Finite k v.1.ResidueField := functionFieldPlaceResidue k F v.1
    let : Finite v.1.ResidueField := Module.finite_of_finite k
    let : Finite (IsLocalRing.ResidueField O) :=
      Finite.of_equiv v.1.ResidueField (curvePlaceCompletionResidueEquiv v.1).toEquiv
    exact hi (hs O (IsLocalRing.ResidueField O)
      (IsScalarTower.toAlgHom (curvePlaceSIntegers k F S) O (IsLocalRing.ResidueField O))
      IsLocalRing.residue_surjective hlarge)

/-- Choose actual original-coefficient factor lifts outside a finite exceptional set. -/
def curvePlaceSmoothConnectedPointLifts
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ E : Finset (CurvePlaceLevelFactorIndex k F S),
      (i : CurvePlaceLevelFactorIndex k F S) → i ∉ E →
        (p : RingPoints (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F S i)) →
          {q : RingPoints (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F S i) //
            RingPoints.map f q = p} :=
  cofiniteSpacePointLifts (CurvePlaceLevelFactor k F S) f
    (curvePlaceSmoothConnectedFactor_eventually_surjective k F S
      hLW hX hXft hY hYft f hf hconn)

/-- Local smooth openness and the exact estimate imply openness on this actual level. -/
theorem curvePlaceSmoothConnectedLevel_isOpenMap
    (hLW : SpaceUniformLangWeilStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (curvePlaceSpaceLevelTopology k F S X)
      (curvePlaceSpaceLevelTopology k F S Y) (RingPoints.map f) :=
  curvePlaceSpaceLevel_isOpenMap_of_smooth k F S completeFieldSmoothSpacePointOpen
    hS hX hXft hY hYft f hf
    (curvePlaceSmoothConnectedFactor_eventually_surjective k F S
      hLW hX hXft hY hYft f hf hconn)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  [Algebra (ULift.{u} ℤ) ((S : Set (FinitePlace K)).integer K)]
  [LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) ((S : Set (FinitePlace K)).integer K))]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- Almost-all surjectivity uses the full factor index, including all infinite places. -/
theorem numberFieldSmoothConnectedFactor_eventually_surjective
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := NumberFieldLevelFactor K S i) f) := by
  classical
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  obtain ⟨c, _, hs⟩ := SmoothDimensionUniformLifts.exists_uniform_henselian_surjectivity
    ((S : Set (FinitePlace K)).integer K) hLW X Y f hX hXft hY hYft hf hconn
  let small : Set {v : FinitePlace K // v ∉ S} :=
    {v | (Nat.card (IsLocalRing.ResidueField (v.1.adicCompletionIntegers K)) : ℝ) ≤ c ^ 2}
  have hsmall : small.Finite :=
    (finitePlaceCompletion_finite_small_residue K (c ^ 2)).preimage
      Subtype.val_injective.injOn
  apply Filter.eventually_cofinite.mpr
  apply (((Set.finite_range
    (Sum.inl : InfinitePlace K → NumberFieldLevelFactorIndex K S)).union
    (Set.finite_range (fun v : {v : FinitePlace K // v ∈ S} =>
      (Sum.inr (Sum.inl v) : NumberFieldLevelFactorIndex K S)))).union
    (hsmall.image (fun v => Sum.inr (Sum.inr v)))).subset
  intro i hi
  rcases i with v | v | v
  · exact Or.inl (Or.inl ⟨v, rfl⟩)
  · exact Or.inl (Or.inr ⟨v, rfl⟩)
  · apply Or.inr
    refine ⟨v, ?_, rfl⟩
    by_contra hv
    have hlarge : c ^ 2 < (Nat.card (IsLocalRing.ResidueField
        (NumberFieldLevelFactor K S (.inr (.inr v)))) : ℝ) := lt_of_not_ge hv
    let O := NumberFieldLevelFactor K S (.inr (.inr v))
    let : HenselianLocalRing O := adicCompletionIntegers_henselian (RingOfIntegers K) K v.1
    let : Finite (IsLocalRing.ResidueField O) := CompletionResidue.finite_adicResidueField K v.1
    exact hi (hs O (IsLocalRing.ResidueField O)
      (IsScalarTower.toAlgHom ((S : Set (FinitePlace K)).integer K)
        O (IsLocalRing.ResidueField O))
      IsLocalRing.residue_surjective hlarge)

/-- Actual point lifts retain the complete number-field index and the original action. -/
def numberFieldSmoothConnectedPointLifts
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ E : Finset (NumberFieldLevelFactorIndex K S),
      (i : NumberFieldLevelFactorIndex K S) → i ∉ E →
        (p : RingPoints ((S : Set (FinitePlace K)).integer K) Y (NumberFieldLevelFactor K S i)) →
          {q : RingPoints ((S : Set (FinitePlace K)).integer K) X (NumberFieldLevelFactor K S i) //
            RingPoints.map f q = p} :=
  cofiniteSpacePointLifts (NumberFieldLevelFactor K S) f
    (numberFieldSmoothConnectedFactor_eventually_surjective K S
      hLW hX hXft hY hYft f hf hconn)

/-- The actual level map is open at finite and infinite factors, without fixed dimension. -/
theorem numberFieldSmoothConnectedLevel_isOpenMap
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (numberFieldSpaceLevelTopology K S X)
      (numberFieldSpaceLevelTopology K S Y) (RingPoints.map f) :=
  numberFieldSpaceLevel_isOpenMap_of_smooth K S completeFieldSmoothSpacePointOpen
    hX hXft hY hYft f hf
    (numberFieldSmoothConnectedFactor_eventually_surjective K S
      hLW hX hXft hY hYft f hf hconn)

end NumberField

end Langlands.Global
