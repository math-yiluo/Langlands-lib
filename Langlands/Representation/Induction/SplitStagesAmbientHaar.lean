import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet

/-! # Ambient subgroup moduli in split induction in stages -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

open Aubert.General MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uA

variable {A : Type uA} [Group A] [TopologicalSpace A]
  {Q L U : Subgroup A} (d : IsSemidirectDecomposition Q L U)
  (P : Subgroup Q) (hker : d.projection.ker ≤ P)

local notation "s" => Subgroup.inclusion d.levi_le
local notation "rP" => splitStagesRetraction d.projection s (fun l => d.projection_levi l) P hker
local notation "N" => MonoidHom.ker rP

/-- Remove the restricted intermediate subgroup and then the ambient
Levi-projection kernel, preserving the original group element. -/
def splitStagesAmbientKernelEquiv : N ≃ₜ* U :=
  (splitStagesKernelContinuousEquiv d.projection s
    (fun l => d.projection_levi l) P hker).trans
      (Aubert.General.CorrectedFiltration.projectionKerEquiv d)

@[simp] theorem splitStagesAmbientKernelEquiv_apply (x : N) :
    (splitStagesAmbientKernelEquiv d P hker x : A) = (((x : P) : Q) : A) := rfl

variable (F : Subgroup A)

local notation "H" => Subgroup.subgroupOf (Q ⊓ F) Q
local notation "HP" => Subgroup.subgroupOf H P
local notation "D" => Subgroup.comap (Subgroup.subtype N) HP

/-- The nested kernel intersection is the original radical intersected
with the original ambient subgroup, with its induced topology. -/
def splitStagesAmbientIntersectionEquiv : D ≃ₜ* (U ⊓ F : Subgroup A) where
  toFun x := ⟨(splitStagesAmbientKernelEquiv d P hker x.val : A),
    (splitStagesAmbientKernelEquiv d P hker x.val).property, x.property.2⟩
  invFun x := ⟨(splitStagesAmbientKernelEquiv d P hker).symm ⟨x, x.property.1⟩,
    d.unipotent_le x.property.1, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp (splitStagesAmbientKernelEquiv d P hker).continuous).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((splitStagesAmbientKernelEquiv d P hker).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

@[simp] theorem splitStagesAmbientIntersectionEquiv_apply (x : D) :
    (splitStagesAmbientIntersectionEquiv d P hker F x : A) =
      ((((x : N) : P) : Q) : A) := rfl

omit [TopologicalSpace A] in
include d in
/-- An intersection with the ambient Levi normalizes the corresponding
intersection with its radical. -/
theorem splitStagesAmbient_normalizes :
    L ⊓ F ≤ Subgroup.normalizer ((U ⊓ F : Subgroup A) : Set A) := by
  intro x hx
  apply Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨d.levi_le_normalizer hx.1, Subgroup.le_normalizer hx.2⟩

variable [IsTopologicalGroup A] [LocallyCompactSpace A]
  (hU : IsClosed (U : Set A)) (hF : IsClosed (F : Set A))
  [LocallyCompactSpace (MonoidHom.ker (splitStagesRetraction d.projection
    (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) P hker))]
  [MeasurableSpace (MonoidHom.ker (splitStagesRetraction d.projection
    (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) P hker))]
  [BorelSpace (MonoidHom.ker (splitStagesRetraction d.projection
    (Subgroup.inclusion d.levi_le) (fun l => d.projection_levi l) P hker))]
  [MeasurableSpace (Subgroup.comap (Subgroup.subtype (MonoidHom.ker
    (splitStagesRetraction d.projection (Subgroup.inclusion d.levi_le)
      (fun l => d.projection_levi l) P hker)))
    (Subgroup.subgroupOf (Subgroup.subgroupOf (Q ⊓ F) Q) P))]
  [BorelSpace (Subgroup.comap (Subgroup.subtype (MonoidHom.ker
    (splitStagesRetraction d.projection (Subgroup.inclusion d.levi_le)
      (fun l => d.projection_levi l) P hker)))
    (Subgroup.subgroupOf (Subgroup.subgroupOf (Q ⊓ F) Q) P))]
  (hsH : ∀ l : Subgroup.comap (Subgroup.inclusion d.levi_le) P,
    Subgroup.inclusion d.levi_le (l : L) ∈ Subgroup.subgroupOf (Q ⊓ F) Q)
  (hHP : IsClosed ((Subgroup.subgroupOf (Subgroup.subgroupOf (Q ⊓ F) Q) P) : Set P))

/-- The exact subgroup-to-kernel Haar character is the original radical
modulus divided by the original radical-intersection modulus. -/
theorem splitStagesAmbientHaarRatio_apply (l : Subgroup.comap s P) :
    splitKernelHaarRatio rP (MonoidHom.subgroupComap s P) HP hsH hHP l =
      HaarModulus.closedRestrictCharacter U hU L d.levi_le_normalizer (l : L) /
        HaarModulus.closedNormalizerCharacter (U ⊓ F) (hU.inter hF)
          ⟨((l : L) : A), splitStagesAmbient_normalizes d F
            ⟨(l : L).property, (hsH l).2⟩⟩ := by
  let : LocallyCompactSpace D := (isClosed_splitKernelIntersection rP HP hHP).locallyCompactSpace
  have hN : mulEquivHaarChar (splitKernelConjugation rP (MonoidHom.subgroupComap s P) l) =
      (HaarModulus.closedRestrictCharacter U hU L d.levi_le_normalizer (l : L) : ℝ≥0)⁻¹ := by
    rw [Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter U hU
      ⟨((l : L) : A)⁻¹, d.levi_le_normalizer (L.inv_mem (l : L).property)⟩
      (splitStagesAmbientKernelEquiv d P hker) _ (fun x => by
        simp only [splitStagesAmbientKernelEquiv_apply, splitKernelConjugation_apply]
        change ((l : L) : A)⁻¹ * (((x : P) : Q) : A) * ((l : L) : A) = _
        rw [inv_inv])]
    rw [← Units.val_inv_eq_inv_val, ← map_inv]
    rfl
  let gC : Subgroup.normalizer ((U ⊓ F : Subgroup A) : Set A) :=
    ⟨((l : L) : A), splitStagesAmbient_normalizes d F
      ⟨(l : L).property, (hsH l).2⟩⟩
  have hD : mulEquivHaarChar
      (splitKernelIntersectionConjugation rP (MonoidHom.subgroupComap s P) HP hsH l) =
      (HaarModulus.closedNormalizerCharacter (U ⊓ F) (hU.inter hF) gC : ℝ≥0)⁻¹ := by
    rw [Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter
      (U ⊓ F) (hU.inter hF) gC⁻¹ (splitStagesAmbientIntersectionEquiv d P hker F) _
      (fun x => by
        simp only [Subgroup.coe_inv, inv_inv]
        change ((((splitKernelConjugation rP (MonoidHom.subgroupComap s P) l (x : N) : N) : P) : Q) : A) =
          ((l : L) : A)⁻¹ * ((((x : N) : P) : Q) : A) * ((l : L) : A)
        rw [splitKernelConjugation_apply]
        rfl)]
    rw [map_inv, Units.val_inv_eq_inv_val]
  apply Units.ext
  rw [splitKernelHaarRatio_apply]
  change mulEquivHaarChar
      (splitKernelIntersectionConjugation rP (MonoidHom.subgroupComap s P) HP hsH l) /
      mulEquivHaarChar (splitKernelConjugation rP (MonoidHom.subgroupComap s P) l) = _
  rw [hD, hN, inv_div_inv]
  rfl

end Langlands.Induction
