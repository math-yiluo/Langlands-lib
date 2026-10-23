import Langlands.AlgebraicGeometry.Picard.DualMapAdditive
import Langlands.AbelianScheme.Rational
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Conditional rational dualization over a base scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} {A B : AbelianScheme S}
variable (hA : HasDualScheme A) (hB : HasDualScheme B)
variable (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)

local notation "FA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "FB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualAB" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB

/-- Extend the actual additive dualization to the existing rational Hom groups. -/
def dualHom0 : Hom0 A B →ₗ[ℚ] Hom0 FB FA :=
  LinearMap.baseChange ℚ
    (dualAbelianSchemeMapAddHom preservation composition unitCoherence associativity comparison
      symmetry stability hA hB additivity MA evaluationA MB evaluationB
      geometryA geometryB).toIntLinearMap

local notation "dual0AB" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hB additivity MA evaluationA MB evaluationB geometryA geometryB

/-- Pure tensors are sent to pure tensors of the actual integral dual map. -/
@[simp] lemma dualHom0_tmul (q : ℚ) (f : A ⟶ B) :
    dual0AB (q ⊗ₜ[ℤ] f) = q ⊗ₜ[ℤ] dualAB f :=
  LinearMap.baseChange_tmul _ _ _

/-- Compatibility with the canonical maps from integral to rational Hom. -/
@[simp] lemma dualHom0_homToHom0 (f : A ⟶ B) :
    dual0AB (homToHom0 f) = homToHom0 (dualAB f) :=
  dualHom0_tmul preservation composition unitCoherence associativity comparison symmetry stability
    hA hB additivity MA evaluationA MB evaluationB geometryA geometryB 1 f

/-- Uniqueness of the rational-linear extension of the same integral dualization. -/
lemma dualHom0_unique (F : Hom0 A B →ₗ[ℚ] Hom0 FB FA)
    (hF : ∀ f : A ⟶ B, F (homToHom0 f) = homToHom0 (dualAB f)) : F = dual0AB := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q f =>
      have h : q ⊗ₜ[ℤ] f = q • homToHom0 f := by
        simp [homToHom0_apply, TensorProduct.smul_tmul']
      rw [h, map_smul, map_smul, hF, dualHom0_homToHom0]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Identity is preserved with the same endpoint data on both sides. -/
@[simp] lemma dualHom0_id
    (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA) :
    dualHom0 preservation composition unitCoherence associativity comparison symmetry stability
      hA hA additivityAA MA evaluationA MA evaluationA geometryA geometryA (id0 A) = id0 FA := by
  change dualHom0 preservation composition unitCoherence associativity comparison symmetry stability
    hA hA additivityAA MA evaluationA MA evaluationA geometryA geometryA
      ((1 : ℚ) ⊗ₜ[ℤ] (𝟙 A)) = (1 : ℚ) ⊗ₜ[ℤ] (𝟙 FA)
  rw [dualHom0_tmul, dualAbelianSchemeMapFromEvaluation_id]

variable {C : AbelianScheme S}
variable (hC : HasDualScheme C)
variable (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
variable (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
  structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))
variable (geometryC : DualSchemeGeometry C hC)
variable (additivityBC : DualSchemeMapAdditivity preservation stability B C hB hC)
variable (additivityAC : DualSchemeMapAdditivity preservation stability A C hA hC)

local notation "FC" => dualAbelianSchemeFromEvaluation C hC geometryC preservation MC
  evaluationC stability composition unitCoherence associativity comparison symmetry
local notation "dual0BC" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hB hC additivityBC MB evaluationB MC evaluationC geometryB geometryC
local notation "dual0AC" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hC additivityAC MA evaluationA MC evaluationC geometryA geometryC

/-- Rational dualization reverses the existing rational composition. -/
lemma dualHom0_comp (f : Hom0 A B) (g : Hom0 B C) :
    dual0AC (comp0 A B C f g) = comp0 FC FB FA (dual0BC g) (dual0AB f) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
      induction g using TensorProduct.inductionOn with
      | tmul r g =>
          simp only [comp0_tmul, dualHom0_tmul, mul_comm q r]
          rw [dualAbelianSchemeMapFromEvaluation_comp (hB := hB) (geometryB := geometryB)
            (MB := MB) (evaluationB := evaluationB)]
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end Langlands.AbelianScheme
