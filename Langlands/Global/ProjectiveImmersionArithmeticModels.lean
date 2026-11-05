import Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionCoefficientBaseChange
import Langlands.Global.AdelicSIntegersColimitProof

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.NoetherianApproximation

private theorem finite_coefficients_in_stage {F : Type u} [CommRing F]
    {V : Type v} (A : Subalgebra ℤ F) (hA : A.FG)
    (B : Finset V → Subring F)
    (hmono : ∀ {S T}, S ⊆ T → B S ≤ B T)
    (hcover : ∀ a : F, ∃ T, a ∈ B T) (S : Finset V) :
    ∃ T, S ⊆ T ∧ A.toSubring ≤ B T := by
  classical
  obtain ⟨s, hs⟩ := hA
  choose support hsupport using hcover
  refine ⟨S ∪ s.biUnion support, Finset.subset_union_left, ?_⟩
  rw [← hs, Algebra.adjoin_int]
  change Subring.closure (s : Set F) ≤ B _
  apply Subring.closure_le.mpr
  intro a ha
  exact hmono ((Finset.subset_biUnion_of_mem support ha).trans
    Finset.subset_union_right) (hsupport a)

/-- An actual arithmetic model retaining a specified immersion over the original
function field, with a finite exceptional set above any prescribed initial set. -/
structure CurvePlaceProjectiveImmersionModelData
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n) where
  exceptional : Finset (AlgebraicCurve.Place k F)
  containsInitial : S ⊆ exceptional
  geometric : letI := (curvePlaceSIntegers k F exceptional).subtype.toAlgebra
    ProjectiveImmersionRingModelData (curvePlaceSIntegers k F exceptional) F X n j

/-- An actual arithmetic model retaining a specified immersion over the original
number field, with a finite exceptional set above any prescribed initial set. -/
structure NumberFieldProjectiveImmersionModelData
    (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n) where
  exceptional : Finset (FinitePlace F)
  containsInitial : S ⊆ exceptional
  geometric : letI := ((exceptional : Set (FinitePlace F)).integer F).toSubring.subtype.toAlgebra
    ProjectiveImmersionRingModelData ((exceptional : Set (FinitePlace F)).integer F) F X n j

/-- Construct an actual S-integer model of a specified projective immersion in
the function-field branch, retaining both original-field comparisons. -/
def curvePlaceProjectiveImmersionModel
    (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n)
    [IsImmersion j] [CompactSpace X] :
    CurvePlaceProjectiveImmersionModelData k F S X n j := by
  classical
  let D := projectiveImmersionSubalgebraModel F X n j
  have hex := finite_coefficients_in_stage D.coefficients D.finiteGeneration
    (curvePlaceSIntegers k F) (fun h => curvePlaceSIntegers_mono k F h)
    (exists_mem_curvePlaceSIntegers k F) S
  let T := Classical.choose hex
  have hT := Classical.choose_spec hex
  letI : Algebra (curvePlaceSIntegers k F T) F :=
    (curvePlaceSIntegers k F T).subtype.toAlgebra
  letI : Algebra D.coefficients (curvePlaceSIntegers k F T) :=
    (Subring.inclusion hT.2).toAlgebra
  letI : IsScalarTower D.coefficients (curvePlaceSIntegers k F T) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨T, hT.1, projectiveImmersionCoefficientBaseChange D
    (curvePlaceSIntegers k F T)⟩

/-- Construct an actual S-integer model of a specified projective immersion in
the number-field branch, retaining both original-field comparisons. -/
def numberFieldProjectiveImmersionModel
    (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F))
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n)
    [IsImmersion j] [CompactSpace X] :
    NumberFieldProjectiveImmersionModelData F S X n j := by
  classical
  let D := projectiveImmersionSubalgebraModel F X n j
  have hex := finite_coefficients_in_stage D.coefficients D.finiteGeneration
    (fun T : Finset (FinitePlace F) => ((T : Set (FinitePlace F)).integer F).toSubring)
    (fun {T U} h => numberFieldSIntegers_mono F (T := T) (U := U) h)
    (exists_mem_numberFieldSIntegers F) S
  let T := Classical.choose hex
  have hT := Classical.choose_spec hex
  letI aRF : Algebra ((T : Set (FinitePlace F)).integer F) F :=
    ((T : Set (FinitePlace F)).integer F).toSubring.subtype.toAlgebra
  letI aAR : Algebra D.coefficients ((T : Set (FinitePlace F)).integer F) :=
    (Subring.inclusion hT.2).toAlgebra
  letI tower : IsScalarTower D.coefficients ((T : Set (FinitePlace F)).integer F) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨T, hT.1, @projectiveImmersionCoefficientBaseChange F _ X n j D
    ((T : Set (FinitePlace F)).integer F) _ aRF aAR tower⟩

end Langlands.Global
