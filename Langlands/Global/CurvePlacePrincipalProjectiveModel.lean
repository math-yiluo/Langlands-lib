import Langlands.Global.CurvePlacePrincipalSIntegerFinite
import Langlands.Global.ExtensionCompatibleProjectiveModels

noncomputable section

universe u v

open CategoryTheory
open _root_.AlgebraicGeometry IntermediateField
open scoped Classical AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.Global

open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.NoetherianApproximation

private theorem coefficients_in_principal_stage {F : Type u} [CommRing F]
    {V : Type v} (A : Subalgebra ℤ F) (hA : A.FG)
    (B : Finset V → Subring F)
    (hmono : ∀ {S T}, S ⊆ T → B S ≤ B T)
    (hcover : ∀ a : F, ∃ T, a ∈ B T) (S : Finset V) :
    ∃ T, S ⊆ T ∧ A.toSubring ≤ B T := by
  obtain ⟨s, hs⟩ := hA
  choose support hsupport using hcover
  refine ⟨S ∪ s.biUnion support, Finset.subset_union_left, ?_⟩
  rw [← hs, Algebra.adjoin_int]
  change Subring.closure (s : Set F) ≤ B _
  apply Subring.closure_le.mpr
  intro a ha
  exact hmono ((Finset.subset_biUnion_of_mem support ha).trans
    Finset.subset_union_right) (hsupport a)

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]

/-- An actual model over the full upper preimage of a principal lower exceptional set. -/
structure CurvePlacePrincipalProjectiveModelData
    (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) where
  denominator : AlgebraicCurve.CurveModel.chartRing k ({s} : Set K)
  denominator_ne_zero : denominator ≠ 0
  containsInitial : S ⊆ curvePlacePrincipalExceptional k K s (denominator : K)
  containsUpper : T ⊆ curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (denominator : K))
  geometric : letI := (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (denominator : K)))).subtype.toAlgebra
    ProjectiveImmersionRingModelData
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (denominator : K)))) L X n j

/-- Construct the original projective model on a finite locally free principal arithmetic level. -/
def curvePlacePrincipalProjectiveModel
    (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n)
    [IsImmersion j] [CompactSpace X] :
    CurvePlacePrincipalProjectiveModelData k K L s S T X n j := by
  let : Algebra (RatFunc k) L :=
    ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
  let : IsScalarTower (RatFunc k) K L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (RatFunc k) L := .of_algebraMap_eq fun a => by
    change algebraMap k L a =
      algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
    rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
      ← IsScalarTower.algebraMap_apply k K L]
  let : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
  let D := projectiveImmersionSubalgebraModel L X n j
  have hex := coefficients_in_principal_stage D.coefficients D.finiteGeneration
    (curvePlaceSIntegers k L) (fun h => curvePlaceSIntegers_mono k L h)
    (exists_mem_curvePlaceSIntegers k L) T
  let U := Classical.choose hex
  have hTU := (Classical.choose_spec hex).1
  have hU := (Classical.choose_spec hex).2
  let V := S ∪ U.image (curvePlaceRestriction (K := K))
  have hUV : U ⊆ curvePlaceExceptionalPreimage (L := L) V :=
    curvePlace_subset_exceptionalPreimage_union_image S U
  have hden := exists_curvePlacePrincipalExceptional_superset k K s V
  let d := Classical.choose hden
  have hd := (Classical.choose_spec hden).1
  have hVW := (Classical.choose_spec hden).2
  let W := curvePlacePrincipalExceptional k K s (d : K)
  have hUW : U ⊆ curvePlaceExceptionalPreimage (L := L) W := by
    intro q hq
    apply (mem_curvePlaceExceptionalPreimage W q).mpr
    exact hVW ((mem_curvePlaceExceptionalPreimage V q).mp (hUV hq))
  have hDW : D.coefficients.toSubring ≤
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) W) :=
    hU.trans (curvePlaceSIntegers_mono k L hUW)
  let B := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) W)
  letI aBL : Algebra B L := B.subtype.toAlgebra
  letI aAB : Algebra D.coefficients B := (Subring.inclusion hDW).toAlgebra
  letI tower : IsScalarTower D.coefficients B L := .of_algebraMap_eq fun _ => rfl
  exact ⟨d, hd, Finset.subset_union_left.trans hVW, hTU.trans hUW,
    @projectiveImmersionCoefficientBaseChange L _ X n j D B _ aBL aAB tower⟩

/-- The given original function-field presentation supplies the parameter automatically. -/
def curvePlaceFunctionFieldProjectiveModel
    (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n)
    [IsImmersion j] [CompactSpace X] :
    CurvePlacePrincipalProjectiveModelData k K L
      (algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)) S T X n j := by
  let a := algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮a⟯ K := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  exact curvePlacePrincipalProjectiveModel k K L a S T X n j

end Langlands.Global
