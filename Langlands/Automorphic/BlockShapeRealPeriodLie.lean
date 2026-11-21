import Langlands.Automorphic.BlockShapeRealLieDecomposition
import Langlands.Automorphic.BlockShapeLeviSliceDifferential
import Langlands.Automorphic.BlockShapePositiveEnveloping
import Langlands.Global.ArchimedeanCompactLieAlgebra
import Langlands.Group.GL.BlockLieDecomposition

/-! Actual block Lie directions at the Levi restriction of a constant term. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Automorphic

open Langlands.Algebra Langlands.Algebra.UniversalEnveloping Langlands.Archimedean
  Langlands.Archimedean.Kostant Langlands.GeneralLinear Langlands.Geometric Langlands.Global
  Langlands.Global.ArchimedeanGL NumberField
open scoped Classical Matrix.Norms.Operator TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] {n : ℕ} (B : BlockShape n)

variable [NumberField F]

local instance periodRealLieRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance periodRealLieContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance periodRealLieFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

private theorem strictUpperBlockLie_entry (X : RealLieAlgebra F n)
    (hX : IsStrictUpperBlockLie F B X) (v : ComplexLieMatrixPlace F)
    (a b : Fin n) (hab : blockIndex B b ≤ blockIndex B a) :
    complexLieProductMatrixCoordinates F n (complexify F n X) v a b = 0 := by
  rw [complexify_apply]
  cases v with
  | inl v =>
    rw [complexLieProductMatrixCoordinates_tmul_real, one_smul]
    change (algebraMap ℝ ℂ) ((realLieAlgebraToMatrix F n X a b).1 v) = 0
    have hz : (realLieAlgebraToMatrix F n X a b).1 v = 0 := by rw [hX a b hab]; rfl
    rw [hz, map_zero]
  | inr v =>
    obtain ⟨v, i⟩ := v
    rw [complexLieProductMatrixCoordinates_tmul_complex, one_smul]
    have hz : complexPlaceLieProjection F n v X a b = 0 := by
      change (realLieAlgebraToMatrix F n X a b).2 v = 0
      rw [hX a b hab]
      rfl
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa only [ComplexGenericLarge.pairHom_zero] using hz
    · rw [ComplexGenericLarge.pairHom_one]
      change star (complexPlaceLieProjection F n v X a b) = 0
      rw [hz, star_zero]

/-- The restriction of the constant term to the Levi kills each actual
strict upper block real Lie direction. -/
theorem blockLeviTermRestriction_strictUpperBlockLie (X : RealLieAlgebra F n)
    (hX : IsStrictUpperBlockLie F B X) (f : FiniteSmoothRationalFunctions F n) :
    blockLeviTermRestriction F B
      (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f) = 0 := by
  let L := ComplexLieMatrixPlace F
  let b := glBasis ℂ (fun _ : L => n)
  let d := blockAdjointWeight B L
  let Y := complexLieProductMatrixCoordinates F n (complexify F n X)
  let U := UniversalEnvelopingAlgebra ℂ (GLProd ℂ (fun _ : L => n))
  let g : GLProd ℂ (fun _ : L => n) →ₗ⁅ℂ⁆ U := UniversalEnvelopingAlgebra.ι ℂ
  have hmem : g Y ∈ positiveWeightRightIdeal b d := by
    rw [← b.sum_repr Y, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [map_smul]
    by_cases hc : 0 < d c
    · exact (positiveWeightRightIdeal b d).smul_mem _
        (Submodule.subset_span ⟨c, hc, 1, (mul_one _).symm⟩)
    · have hab : blockIndex B c.2.2 ≤ blockIndex B c.2.1 :=
        le_of_not_gt fun h => hc ((blockAdjointWeight_pos_iff B c).mpr h)
      have he : b.repr Y c = 0 := by
        rw [show b = glBasis ℂ (fun _ : L => n) from rfl, glBasis_repr]
        exact strictUpperBlockLie_entry F B X hX c.1 c.2.1 c.2.2 hab
      rw [he, zero_smul]
      exact Submodule.zero_mem _
  have h := blockLeviTermRestriction_positiveIdeal_eq_zero F B f hmem
  change blockLeviTermRestriction F B (finiteSmoothEnvelopingAction F n
    (LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F n).symm
      (UniversalEnvelopingAlgebra.ι ℂ Y)) f) = 0 at h
  rw [LieEnvelopingEquiv.enveloping_generator,
    show (complexLieProductMatrixCoordinates F n).symm Y = complexify F n X from
      (complexLieProductMatrixCoordinates F n).symm_apply_apply _] at h
  exact h

end Langlands.Automorphic
