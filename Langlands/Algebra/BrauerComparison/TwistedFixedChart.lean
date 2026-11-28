import Langlands.Algebra.BrauerComparison.BaseChangeChart
import Langlands.Algebra.GaloisTwistedMatrix

/-! # Twisted fixed matrices from a splitting chart -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u

namespace Langlands.BrauerComparison

open Algebra.GaloisTwistedMatrix CentralSimple

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {A : CSA.{u, u} K} {I : Type} [Fintype I] [DecidableEq I]

/-- Embed the original algebra in the split matrices using the supplied chart. -/
def splittingChartEmbedding (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) : A →ₐ[K] Matrix I I L :=
  (e.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight

@[simp] theorem splittingChartEmbedding_apply (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (a : A) :
    splittingChartEmbedding e a = e (1 ⊗ₜ[K] a) := rfl

theorem splittingChartEmbedding_injective (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    Function.Injective (splittingChartEmbedding e) :=
  e.injective.comp (Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective)

/-- The original algebra in a splitting chart spans the matrices over the splitting field. -/
theorem span_splittingChartEmbedding (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    Submodule.span L ((splittingChartEmbedding e).range : Set (Matrix I I L)) = ⊤ := by
  rw [eq_top_iff]
  intro X hX
  obtain ⟨Y, rfl⟩ := e.surjective X
  clear hX
  induction Y with
  | tmul l a =>
    have h : l ⊗ₜ[K] a = l • ((1 : L) ⊗ₜ[K] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, ← splittingChartEmbedding_apply]
    exact Submodule.smul_mem _ l (Submodule.subset_span ⟨a, rfl⟩)
  | add Y Z hY hZ =>
    rw [map_add]
    exact Submodule.add_mem _ hY hZ

variable (M : Type u) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K L]

/-- The inverse of the original conjugating lift, extended at the restricted automorphism. -/
def extendedInverseLift (P : Gal(L/K) → GL I L) (σ : Gal(M/K)) : GL I M :=
  GeneralLinearGroup.map (algebraMap L M) ((P (σ.restrictNormal L))⁻¹)

variable {e : L ⊗[K] A ≃ₐ[L] Matrix I I L} {P : Gal(L/K) → GL I L}
  (hact : ∀ s X, (splittingChartIndexAction e).act s X =
    (P s : Matrix I I L) * X.map s * ((P s)⁻¹ : GL I L))

include hact in
/-- The embedded algebra satisfies the twisted fixed equations over the larger field. -/
theorem range_enlargedSplittingChart_le_twistedFixed :
    (splittingChartEmbedding (enlargedSplittingChart M e)).range ≤
      twistedFixed (fun σ => (extendedInverseLift M P σ : Matrix I I M)) := by
  rintro _ ⟨a, rfl⟩ σ
  let Y := e (1 ⊗ₜ[K] a)
  let s := σ.restrictNormal L
  have hY : (P s : Matrix I I L) * Y.map s * ((P s)⁻¹ : GL I L) = Y := by
    rw [← hact, splittingChartIndexAction_apply, tensorCoefficientMap_tmul, map_one]
  have hcomm : (↑((P s)⁻¹ : GL I L) : Matrix I I L) * Y =
      Y.map s * ((P s)⁻¹ : GL I L) := by
    calc
      _ = (↑((P s)⁻¹ : GL I L) : Matrix I I L) *
          ((P s : Matrix I I L) * Y.map s * ((P s)⁻¹ : GL I L)) :=
        congrArg (fun Z : Matrix I I L => (↑((P s)⁻¹ : GL I L) : Matrix I I L) * Z) hY.symm
      _ = _ := by
        rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hmap : (Y.map (algebraMap L M)).map σ = (Y.map s).map (algebraMap L M) := by
    ext i j
    exact (σ.restrictNormal_commutes L (Y i j)).symm
  have hemb : splittingChartEmbedding (enlargedSplittingChart M e) a =
      Y.map (algebraMap L M) := by
    rw [splittingChartEmbedding_apply, enlargedSplittingChart_tmul, one_smul]
  change (extendedInverseLift M P σ : Matrix I I M) *
      splittingChartEmbedding (enlargedSplittingChart M e) a =
    (splittingChartEmbedding (enlargedSplittingChart M e) a).map σ *
      (extendedInverseLift M P σ : Matrix I I M)
  rw [hemb, hmap]
  change ((↑((P s)⁻¹ : GL I L) : Matrix I I L).map (algebraMap L M)) *
      Y.map (algebraMap L M) =
    (Y.map s).map (algebraMap L M) * ((↑((P s)⁻¹ : GL I L) : Matrix I I L).map (algebraMap L M))
  rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm]

variable [IsGalois K M]

include hact in
/-- The embedded algebra is the full algebra satisfying the twisted fixed equations. -/
theorem range_enlargedSplittingChart_eq_twistedFixed :
    (splittingChartEmbedding (enlargedSplittingChart M e)).range =
      twistedFixed (fun σ => (extendedInverseLift M P σ : Matrix I I M)) := by
  let T : Gal(M/K) → Matrix I I M := fun σ => extendedInverseLift M P σ
  let B := (splittingChartEmbedding (enlargedSplittingChart M e)).range
  have hle : B ≤ twistedFixed T := range_enlargedSplittingChart_le_twistedFixed M hact
  refine le_antisymm hle fun X hX => ?_
  apply mem_of_mem_span T (fun σ => (extendedInverseLift M P σ).isUnit) (twistedFixed T)
    le_rfl B.toSubmodule hle hX
  rw [show (B.toSubmodule : Set (Matrix I I M)) = (B : Set (Matrix I I M)) from rfl,
    span_splittingChartEmbedding]
  exact Submodule.mem_top

/-- The chart identifies the original algebra with the upper twisted fixed algebra. -/
def twistedFixedEnlargedChartEquiv :
    A ≃ₐ[K] twistedFixed (fun σ => (extendedInverseLift M P σ : Matrix I I M)) :=
  (AlgEquiv.ofInjective _ (splittingChartEmbedding_injective (enlargedSplittingChart M e))).trans
    (Subalgebra.equivOfEq _ _ (range_enlargedSplittingChart_eq_twistedFixed M hact))

end Langlands.BrauerComparison
