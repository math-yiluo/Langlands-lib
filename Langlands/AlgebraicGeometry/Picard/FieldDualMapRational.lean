import Langlands.AlgebraicGeometry.Picard.FieldDualMapAdditive
import Langlands.AbelianScheme.Rational
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Conditional rational dualization over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (additivity : FieldDualSchemeMapAdditivityStatement.{u})
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable {k : Type u} [Field k]
variable {A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
variable (hA : HasDualScheme A) (hB : HasDualScheme B)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

variable (geometry : FieldDualSchemeGeometryStatement.{u})

local notation "FA" => fieldDualAbelianSchemeFromEvaluation geometry A hA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "FB" => fieldDualAbelianSchemeFromEvaluation geometry B hB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualAB" => fieldDualAbelianSchemeMapFromEvaluation geometry hA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry hB MB evaluationB

/-- Scalar extension of the actual additive dualization to the existing rational Hom groups. -/
def fieldDualHom0 : Hom0 A B →ₗ[ℚ] Hom0 FB FA :=
  LinearMap.baseChange ℚ
    (fieldDualAbelianSchemeMapAddHom additivity preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB geometry).toIntLinearMap

local notation "dual0AB" => fieldDualHom0 additivity preservation composition unitCoherence
  associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB geometry

/-- The rational dual sends q tensor f to q tensor the actual dual map of f. -/
@[simp] lemma fieldDualHom0_tmul (q : ℚ) (f : A ⟶ B) :
    dual0AB (q ⊗ₜ[ℤ] f) = q ⊗ₜ[ℤ] dualAB f :=
  LinearMap.baseChange_tmul _ _ _

/-- Compatibility with the canonical integral-to-rational maps. -/
@[simp] lemma fieldDualHom0_homToHom0 (f : A ⟶ B) :
    dual0AB (homToHom0 f) = homToHom0 (dualAB f) :=
  fieldDualHom0_tmul additivity preservation composition unitCoherence associativity comparison
    symmetry stability hA hB MA evaluationA MB evaluationB geometry 1 f

/-- Uniqueness of the rational-linear extension of the same integral dualization. -/
lemma fieldDualHom0_unique (F : Hom0 A B →ₗ[ℚ] Hom0 FB FA)
    (hF : ∀ f : A ⟶ B, F (homToHom0 f) = homToHom0 (dualAB f)) : F = dual0AB := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q f =>
      have h : q ⊗ₜ[ℤ] f = q • homToHom0 f := by
        simp [homToHom0_apply, TensorProduct.smul_tmul']
      rw [h, map_smul, map_smul, hF, fieldDualHom0_homToHom0]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Identity is preserved when the same endpoint data are used on both sides. -/
@[simp] lemma fieldDualHom0_id :
    fieldDualHom0 additivity preservation composition unitCoherence associativity comparison
      symmetry stability hA hA MA evaluationA MA evaluationA geometry (id0 A) = id0 FA := by
  change fieldDualHom0 additivity preservation composition unitCoherence associativity comparison
    symmetry stability hA hA MA evaluationA MA evaluationA geometry
      ((1 : ℚ) ⊗ₜ[ℤ] (𝟙 A)) = (1 : ℚ) ⊗ₜ[ℤ] (𝟙 FA)
  rw [fieldDualHom0_tmul, fieldDualAbelianSchemeMapFromEvaluation_id]

variable {C : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
variable (hC : HasDualScheme C)
variable (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
variable (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
  structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))

local notation "FC" => fieldDualAbelianSchemeFromEvaluation geometry C hC preservation MC
  evaluationC stability composition unitCoherence associativity comparison symmetry
local notation "dual0BC" => fieldDualHom0 additivity preservation composition unitCoherence
  associativity comparison symmetry stability hB hC MB evaluationB MC evaluationC geometry
local notation "dual0AC" => fieldDualHom0 additivity preservation composition unitCoherence
  associativity comparison symmetry stability hA hC MA evaluationA MC evaluationC geometry

/-- Rational dualization reverses the actual rational composition. -/
lemma fieldDualHom0_comp (f : Hom0 A B) (g : Hom0 B C) :
    dual0AC (comp0 A B C f g) = comp0 FC FB FA (dual0BC g) (dual0AB f) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
      induction g using TensorProduct.inductionOn with
      | tmul r g =>
          simp only [comp0_tmul, fieldDualHom0_tmul, mul_comm q r]
          rw [fieldDualAbelianSchemeMapFromEvaluation_comp (hB := hB) (MB := MB)
            (evaluationB := evaluationB)]
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end Langlands.AbelianScheme
