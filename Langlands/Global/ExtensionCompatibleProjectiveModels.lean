import Langlands.Global.ArithmeticExceptionalSets
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionCoefficientBaseChange

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped Classical

namespace Langlands.Global

open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.NoetherianApproximation

private theorem coefficients_in_stage {F : Type u} [CommRing F]
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

section Curve

variable (k K L : Type u) [Field k] [PerfectField k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]

/-- An actual upper model at the full preimage of a finite lower exceptional set. -/
structure CurvePlaceExtensionProjectiveModelData
    (S : Finset (AlgebraicCurve.Place k K))
    (T : Finset (AlgebraicCurve.Place k L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) where
  exceptional : Finset (AlgebraicCurve.Place k K)
  containsInitial : S ⊆ exceptional
  containsUpper : T ⊆ curvePlaceExceptionalPreimage (L := L) exceptional
  geometric : letI :=
      (curvePlaceSIntegers k L
        (curvePlaceExceptionalPreimage (L := L) exceptional)).subtype.toAlgebra
    ProjectiveImmersionRingModelData
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) exceptional))
      L X n j

/-- Construct the extension-compatible quasi-projective arithmetic model. -/
def curvePlaceExtensionProjectiveModel
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    (S : Finset (AlgebraicCurve.Place k K))
    (T : Finset (AlgebraicCurve.Place k L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n)
    [IsImmersion j] [CompactSpace X] :
    CurvePlaceExtensionProjectiveModelData k K L S T X n j := by
  let D := projectiveImmersionSubalgebraModel L X n j
  have hex := coefficients_in_stage D.coefficients D.finiteGeneration
    (curvePlaceSIntegers k L) (fun h => curvePlaceSIntegers_mono k L h)
    (exists_mem_curvePlaceSIntegers k L) T
  let U := Classical.choose hex
  have hTU := (Classical.choose_spec hex).1
  have hU := (Classical.choose_spec hex).2
  let V := S ∪ U.image (curvePlaceRestriction (K := K))
  have hUV : U ⊆ curvePlaceExceptionalPreimage (L := L) V :=
    curvePlace_subset_exceptionalPreimage_union_image S U
  have hDV : D.coefficients.toSubring ≤
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) V) :=
    hU.trans (curvePlaceSIntegers_mono k L hUV)
  let R := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) V)
  letI aRL : Algebra R L := R.subtype.toAlgebra
  letI aAR : Algebra D.coefficients R := (Subring.inclusion hDV).toAlgebra
  letI tower : IsScalarTower D.coefficients R L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨V, Finset.subset_union_left, hTU.trans hUV,
    @projectiveImmersionCoefficientBaseChange L _ X n j D R _ aRL aAR tower⟩

end Curve

section NumberField

variable (K L : Type u) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- An actual upper number-field model at the full preimage of a lower set. -/
structure NumberFieldExtensionProjectiveModelData
    (S : Finset (FinitePlace K)) (T : Finset (FinitePlace L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) where
  exceptional : Finset (FinitePlace K)
  containsInitial : S ⊆ exceptional
  containsUpper : T ⊆ numberFieldExceptionalPreimage (L := L) exceptional
  geometric : letI :=
      (((numberFieldExceptionalPreimage (L := L) exceptional :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L).toSubring.subtype.toAlgebra
    ProjectiveImmersionRingModelData
      (((numberFieldExceptionalPreimage (L := L) exceptional :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) L X n j

/-- Construct the number-field model at exactly the full upper exceptional set. -/
def numberFieldExtensionProjectiveModel
    (S : Finset (FinitePlace K)) (T : Finset (FinitePlace L))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n)
    [IsImmersion j] [CompactSpace X] :
    NumberFieldExtensionProjectiveModelData K L S T X n j := by
  let D := projectiveImmersionSubalgebraModel L X n j
  have hex := coefficients_in_stage D.coefficients D.finiteGeneration
    (fun U : Finset (FinitePlace L) => ((U : Set (FinitePlace L)).integer L).toSubring)
    (fun {U V} h => numberFieldSIntegers_mono L (T := U) (U := V) h)
    (exists_mem_numberFieldSIntegers L) T
  let U := Classical.choose hex
  have hTU := (Classical.choose_spec hex).1
  have hU := (Classical.choose_spec hex).2
  let V := S ∪ U.image (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K))
  have hUV : U ⊆ numberFieldExceptionalPreimage (L := L) V :=
    numberField_subset_exceptionalPreimage_union_image S U
  have hDV : D.coefficients.toSubring ≤
      (((numberFieldExceptionalPreimage (L := L) V :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L).toSubring :=
    hU.trans (numberFieldSIntegers_mono L hUV)
  let R := (((numberFieldExceptionalPreimage (L := L) V :
    Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  letI aRL : Algebra R L := R.toSubring.subtype.toAlgebra
  letI aAR : Algebra D.coefficients R := (Subring.inclusion hDV).toAlgebra
  letI tower : IsScalarTower D.coefficients R L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨V, Finset.subset_union_left, hTU.trans hUV,
    @projectiveImmersionCoefficientBaseChange L _ X n j D R _ aRL aAR tower⟩

end NumberField

end Langlands.Global
