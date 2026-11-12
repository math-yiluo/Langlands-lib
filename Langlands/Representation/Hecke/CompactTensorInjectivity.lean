import Langlands.Representation.Hecke.CompactTensorCosetAveraging
import Mathlib.GroupTheory.DoubleCoset

/-! # Injectivity of the prescribed elementary comparison on the original tensor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MulOpposite Classical

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis Langlands.Algebra

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- A reducible name for the exact original balanced tensor with its prescribed actions. -/
abbrev comparisonTensor : Type (max uG v) := by
  letI := rightModule μG μH H.subtype continuous_subtype_val
  letI := heckeNonUnitalModule μH ρ hρ
  exact NonUnitalModuleTensor.Tensor (HeckeAlgebra μH) (HeckeAlgebra μG) V

/-- The original pure tensor, with the prescribed actions made explicit. -/
abbrev comparisonTensorTmul (T : HeckeAlgebra μG) (w : V) :
    comparisonTensor H μG μH ρ hρ := by
  letI := rightModule μG μH H.subtype continuous_subtype_val
  letI := heckeNonUnitalModule μH ρ hρ
  exact NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T w

/-- A finite additive reconstruction from the actual values at chosen
double-coset representatives. -/
def finiteCosetReconstruction (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (s : Finset (DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G))) :
    Induction.CompactFunctions H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) →+
      comparisonTensor H μG μH ρ hρ := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  let ev (q : DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)) :
      Induction.CompactFunctions H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) →+ V :=
    { toFun := fun f => Induction.eval H _ f.val q.out
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact ∑ q ∈ s,
    (NonUnitalModuleTensor.biadditive (HeckeAlgebra μH) (HeckeAlgebra μG) V
      (normalizedSourceCosetTest H μG μH K hK q.out)).comp (ev q)

theorem finiteCosetReconstruction_apply (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G))
    (s : Finset (DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)))
    (f : Induction.CompactFunctions H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ)) :
    finiteCosetReconstruction H μG μH ρ hρ K hK s f =
      ∑ q ∈ s,
        comparisonTensorTmul H μG μH ρ hρ
          (normalizedSourceCosetTest H μG μH K hK q.out) (Induction.eval H _ f.val q.out) := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  simp only [finiteCosetReconstruction, AddMonoidHom.coe_finsetSum, Finset.sum_apply, AddMonoidHom.comp_apply,
    NonUnitalModuleTensor.biadditive_apply]
  rfl

/-- A source-coset comparison vanishes at representatives of other double cosets. -/
theorem compactComparisonValue_sourceCoset_zero (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x y : G) (w : V)
    (hxy : DoubleCoset.mk H K.toSubgroup y ≠ DoubleCoset.mk H K.toSubgroup x) :
    compactComparisonValue H hH μH ρ hρ
      (HeckeAlgebra.toTestFunction μG (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹))
      w y = 0 := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  have ht : compactSubgroupTest H hH y
      (HeckeAlgebra.toTestFunction μG (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹)) = 0 := by
    ext h
    have hn : y⁻¹ * (h : G) * x ∉ K := by
      intro hk
      apply hxy
      apply Eq.symm
      apply DoubleCoset.eq.mpr
      refine ⟨h, h.property, (y⁻¹ * (h : G) * x)⁻¹, K.inv_mem hk, ?_⟩
      group
    change ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) *
      (K : Set G).indicator (fun _ => (1 : ℂ)) ((y⁻¹ * (h : G)) * (x⁻¹)⁻¹) = 0
    simp only [inv_inv]
    simp [hn]
  unfold compactComparisonValue
  rw [ht, map_zero]
  rfl

variable (F :
    comparisonTensor H μG μH ρ hρ →+
      Induction.CompactFunctions H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ))
  (hF : ∀ (T : HeckeAlgebra μG) (w : V),
    F (comparisonTensorTmul H μG μH ρ hρ T w) =
      compactComparisonFunction H hH μH ρ hρ (HeckeAlgebra.toTestFunction μG T) w)

include hF

/-- Each source-coset tensor is recovered at the chosen representative of its
double coset, using its actual image under the additive comparison. -/
theorem tensor_sourceCoset_chosen_value (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (w : V) :
    let q := DoubleCoset.mk H K.toSubgroup x
    comparisonTensorTmul H μG μH ρ hρ
      (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w =
        comparisonTensorTmul H μG μH ρ hρ
          (normalizedSourceCosetTest H μG μH K hK q.out)
          (Induction.eval H _
            (F (comparisonTensorTmul H μG μH ρ hρ
              (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w)).val q.out) := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  let q := DoubleCoset.mk H K.toSubgroup x
  obtain ⟨h, hh, k, hk, hx⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' q)
  let w' := haarScale h • ρ (⟨h, hh⟩ : H)⁻¹ w
  have he :
      comparisonTensorTmul H μG μH ρ hρ
        (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w =
      comparisonTensorTmul H μG μH ρ hρ
        (HeckeAlgebra.rightCosetIndicator μG K hK q.out⁻¹) w' := by
    rw [hx]
    exact tensor_sourceCoset_representative H μG μH ρ hρ K hK q.out ⟨h, hh⟩ ⟨k, hk⟩ w
  rw [he]
  rw [hF]
  exact tensor_sourceCoset_value H hH μG μH ρ hρ K hK q.out w'

/-- A finite reconstruction containing the relevant double coset recovers its
source-coset tensor exactly. -/
theorem finiteCosetReconstruction_sourceCoset (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G))
    (s : Finset (DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)))
    (x : G) (w : V) (hx : DoubleCoset.mk H K.toSubgroup x ∈ s) :
    finiteCosetReconstruction H μG μH ρ hρ K hK s
      (F (comparisonTensorTmul H μG μH ρ hρ
        (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w)) =
      comparisonTensorTmul H μG μH ρ hρ
        (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  rw [finiteCosetReconstruction_apply, Finset.sum_eq_single (DoubleCoset.mk H K.toSubgroup x)]
  · exact (tensor_sourceCoset_chosen_value H hH μG μH ρ hρ F hF K hK x w).symm
  · intro q _ hq
    have hne : DoubleCoset.mk H K.toSubgroup q.out ≠ DoubleCoset.mk H K.toSubgroup x := by
      simpa only [DoubleCoset.out_eq'] using hq
    have hz : Induction.eval H _
        (F (comparisonTensorTmul H μG μH ρ hρ
          (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w)).val q.out = 0 := by
      rw [hF]
      exact compactComparisonValue_sourceCoset_zero H hH μG μH ρ hρ K hK x q.out w hne
    rw [hz]
    exact NonUnitalModuleTensor.tmul_zero _ _ _ _
  · exact fun hn => absurd hx hn

/-- Every additive map from the original Hecke tensor with the prescribed
elementary comparison values is injective. -/
theorem compactComparison_injective_of_pure_values : Function.Injective F := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
  obtain ⟨K, hK, n, s, w, hform⟩ :=
    tensor_finite_coset_normal_form μG μH H.subtype continuous_subtype_val ρ hρ t
  let S : Finset (DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)) :=
    Finset.univ.biUnion fun i : Fin n =>
      (s i).image (fun q => DoubleCoset.mk H K.toSubgroup q.out⁻¹)
  let J := finiteCosetReconstruction H μG μH ρ hρ K hK S
  have hS (i : Fin n) (q : Induction.LeftQuotient K.toSubgroup) (hq : q ∈ s i) :
      DoubleCoset.mk H K.toSubgroup q.out⁻¹ ∈ S :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  have hrec : J (F t) = t := by
    rw [hform]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro q hq
    simpa only [inv_inv] using
      finiteCosetReconstruction_sourceCoset H hH μG μH ρ hρ F hF
        K hK S q.out⁻¹ (w i q) (hS i q hq)
  rw [ht, map_zero] at hrec
  exact hrec.symm

end Langlands.Hecke.Homomorphism
