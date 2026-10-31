import Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient
import Langlands.Representation.Geometric.GeneralCorrectionCharacters
import Langlands.Representation.Parabolic.UnipotentFiniteContainment

/-! Topological transport from the actual orbit kernels to ambient matrix subgroups. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uF

section HaarConjugacy

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]

/-- Continuous conjugacy preserves the actual Haar scaling character. -/
theorem haarChar_eq_of_conjugacy (e : G ≃ₜ* H) (a : G ≃ₜ* G) (b : H ≃ₜ* H)
    (h : ∀ g, e (a g) = b (e g)) :
    mulEquivHaarChar a = mulEquivHaarChar b := by
  let μ : Measure G := haar
  let ν : Measure H := μ.map e
  have : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  have : ν.Regular := Regular.map e.toHomeomorph
  have he : Measurable (e : G → H) := e.continuous.measurable
  have ha : Measurable (a : G → G) := a.continuous.measurable
  have hb : Measurable (b : H → H) := b.continuous.measurable
  have hcoord : b ∘ e = e ∘ a := funext fun g => (h g).symm
  have hscale : mulEquivHaarChar a • ν.map b = ν := by
    calc
      _ = (mulEquivHaarChar a • μ.map a).map e := by
        rw [Measure.map_smul _ he.aemeasurable]
        congr 1
        change (μ.map e).map b = (μ.map a).map e
        rw [Measure.map_map hb he, hcoord, ← Measure.map_map he ha]
      _ = ν := by rw [mulEquivHaarChar_smul_map μ a]
  symm
  rw [mulEquivHaarChar_eq ν]
  have hs := haarScalarFactor_smul (ν.map b) (ν.map b) (c := mulEquivHaarChar a)
  rw! [hscale] at hs
  simpa using hs

end HaarConjugacy

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

omit [IsTopologicalRing F] in
@[simp] theorem parabolicOrbitRadicalAmbientEquiv_apply (u : C.unipotentRadical F) :
    (C.unipotentRadicalAmbientEquiv F u : GeneralLinear n F) = u.val.val := rfl

/-- The radical-stabilizer intersection is the literal target correction subgroup. -/
def parabolicOrbitIntersectionAmbientEquiv :
    parabolicOrbitRadicalIntersection F B C w ≃ₜ*
      intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹ where
  toFun u := ⟨u.val.val.val, ⟨u.val.val, u.val.property, rfl⟩, u.property⟩
  invFun u := ⟨(C.unipotentRadicalAmbientEquiv F).symm ⟨u.val, u.property.1⟩,
    u.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((C.unipotentRadicalAmbientEquiv F).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

omit [IsTopologicalRing F] in
@[simp] theorem parabolicOrbitIntersectionAmbientEquiv_apply
    (u : parabolicOrbitRadicalIntersection F B C w) :
    (parabolicOrbitIntersectionAmbientEquiv F B C w u : GeneralLinear n F) =
      u.val.val.val := rfl

/-- The actual nested kernel has the same topology as the ambient target radical. -/
def parabolicOrbitNestedKernelAmbientEquiv :
    (parabolicOrbitStagesRetraction F B C w).ker ≃ₜ* C.unipotentSubgroup F :=
  (splitStagesKernelContinuousEquiv (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStages_kernel_le F B C w)).trans
      (C.unipotentRadicalAmbientEquiv F)

/-- Removing all intermediate subtypes identifies the actual nested intersection
with the literal target correction subgroup. -/
def parabolicOrbitNestedIntersectionAmbientEquiv :
    parabolicOrbitNestedIntersection F B C w ≃ₜ*
      intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹ :=
  (splitStagesIntersectionContinuousEquiv (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w) (parabolicOrbitStages_kernel_le F B C w)).trans
      (parabolicOrbitIntersectionAmbientEquiv F B C w)

end Langlands.Geometric
