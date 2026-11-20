import Langlands.BaseChange.SplitTensorCuspFormStatement
import Langlands.Global.RankinSelberg.UnipotentClassDecomposition
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Split tensor products of test functions and cusp forms

The coordinate isomorphism for general linear groups restricts to the block
unipotent subgroups. Finite-product integration then gives vanishing of the
constant term when one factor has vanishing constant terms.
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped BigOperators

namespace Langlands.BaseChange

open HarmonicAnalysis
open Global.RankinSelbergGlobal.UnipotentClass (glPiEquiv)

universe u

section Coordinates

variable {F : Type u} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F] {n l : ℕ}

private theorem mem_unipotentSubgroup_iff_coordinates (B : GeneralLinear.BlockShape n)
    (g : GeneralLinear n (Fin l → F)) :
    g ∈ B.unipotentSubgroup (Fin l → F) ↔
      ∀ k, glPiEquiv n (fun _ : Fin l => F) g k ∈ B.unipotentSubgroup F := by
  simp only [B.mem_unipotentSubgroup_iff, B.mem_parabolic_iff]
  constructor
  · rintro ⟨hlower, hdiag⟩ k
    refine ⟨fun i j a b hij => congrFun (hlower i j a b hij) k, ?_⟩
    intro i a b
    have hk := congrFun (hdiag i a b) k
    change g (B.index i a) (B.index i b) k = _
    by_cases hab : a = b <;>
      simpa only [hab, ite_true, ite_false, Pi.one_apply, Pi.zero_apply] using hk
  · intro h
    refine ⟨fun i j a b hij => funext fun k => (h k).1 i j a b hij, ?_⟩
    intro i a b
    funext k
    have hk := (h k).2 i a b
    change g (B.index i a) (B.index i b) k = _ at hk
    by_cases hab : a = b <;>
      simpa only [hab, ite_true, ite_false, Pi.one_apply, Pi.zero_apply] using hk

/-- Restrict the coordinate isomorphism to the unipotent radical of a fixed block shape. -/
private def unipotentPiEquiv (B : GeneralLinear.BlockShape n) :
    B.unipotentSubgroup (Fin l → F) ≃ₜ* (Fin l → B.unipotentSubgroup F) := by
  let e := glPiEquiv n (fun _ : Fin l => F)
  refine
    { toFun := fun v i =>
        ⟨e v.val i, (mem_unipotentSubgroup_iff_coordinates B v.val).mp v.property i⟩
      invFun := fun w => ⟨e.symm (fun i => (w i).val), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (mem_unipotentSubgroup_iff_coordinates B _).mpr
    intro i
    change e (e.symm (fun j => (w j).val)) i ∈ B.unipotentSubgroup F
    rw [e.apply_symm_apply]
    exact (w i).property
  · intro v
    exact Subtype.ext (e.symm_apply_apply v.val)
  · intro w
    funext i
    exact Subtype.ext (congrFun (e.apply_symm_apply (fun j => (w j).val)) i)
  · intro v w
    funext i
    exact Subtype.ext (congrFun (e.map_mul v.val w.val) i)
  · exact continuous_pi fun i =>
      ((continuous_apply i).comp (e.continuous.comp continuous_subtype_val)).subtype_mk _
  · exact (e.symm.continuous.comp (continuous_pi fun i =>
      continuous_subtype_val.comp (continuous_apply i))).subtype_mk _

private theorem splitTensor_mem (φ : Fin l → SchwartzBruhat (GeneralLinear n F)) :
    splitTensor (fun i => (φ i : GeneralLinear n F → ℂ)) ∈
      schwartzBruhatSubmodule (GeneralLinear n (Fin l → F)) := by
  let e := glPiEquiv n (fun _ : Fin l => F)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have h : ∀ᶠ g' in 𝓝 g, ∀ i, φ i (e g' i) = φ i (e g i) :=
      eventually_all.mpr fun i =>
        ((φ i).locallyConstant.comp_continuous
          ((continuous_apply i).comp e.continuous)).eventually_eq g
    filter_upwards [h] with g' hg'
    exact Finset.prod_congr rfl fun i _ => hg' i
  · let K := Set.univ.pi (fun i => tsupport (φ i : GeneralLinear n F → ℂ))
    have hK : IsCompact (e ⁻¹' K) :=
      e.toHomeomorph.isClosedEmbedding.isCompact_preimage
        (isCompact_univ_pi fun i => (φ i).hasCompactSupport)
    have hclosed : IsClosed (e ⁻¹' K) :=
      (isClosed_set_pi fun i _ => isClosed_tsupport (φ i : GeneralLinear n F → ℂ)).preimage
        e.continuous
    refine hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ hclosed)
    intro g hg
    refine Set.mem_univ_pi.mpr (fun i => subset_tsupport _ ?_)
    exact fun hi => hg (Finset.prod_eq_zero (Finset.mem_univ i) hi)

end Coordinates

/-- The published split tensor product is a test function and inherits vanishing constant terms
from any factor with vanishing constant terms. -/
theorem splitTensorCuspForm : SplitTensorCuspFormStatement.{u} := by
  intro F _ _ _ _ n l φ
  let : T2Space F := GeneralLocalField.t2Space F
  have htest := splitTensor_mem φ
  refine ⟨htest, ?_⟩
  intro i₀ hcusp
  let : MeasurableSpace (GeneralLinear n (Fin l → F)) := borel _
  let : BorelSpace (GeneralLinear n (Fin l → F)) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  intro B hB μ hμ
  let : μ.IsHaarMeasure := hμ
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · let f : SchwartzBruhat (GeneralLinear n (Fin l → F)) := ⟨_, htest⟩
    let t := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)
    have ht : IsClosedEmbedding (fun v : B.unipotentSubgroup (Fin l → F) =>
        x * (v : GeneralLinear n (Fin l → F)) * y) :=
      t.isClosedEmbedding.comp (B.isClosed_unipotentSubgroup _).isClosedEmbedding_subtypeVal
    exact (f.continuous.comp ht.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_isClosedEmbedding ht)
  · let : SecondCountableTopology F := GeneralLocalField.secondCountableTopology F
    let : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
    let : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    let : SecondCountableTopology (GeneralLinear n F) :=
      Units.isInducing_embedProduct.secondCountableTopology
    let : SecondCountableTopology (B.unipotentSubgroup F) :=
      IsEmbedding.subtypeVal.secondCountableTopology
    let : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
      inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
    let : LocallyCompactSpace (B.unipotentSubgroup F) :=
      (B.isClosed_unipotentSubgroup F).locallyCompactSpace
    let e := unipotentPiEquiv (l := l) (F := F) B
    let ν : Measure (B.unipotentSubgroup F) := Measure.haar
    let : ν.IsHaarMeasure := inferInstanceAs Measure.haar.IsHaarMeasure
    let : ∀ _ : Fin l, SigmaFinite ν := fun _ => inferInstance
    let νprod : Measure (Fin l → B.unipotentSubgroup F) := Measure.pi (fun _ => ν)
    let : νprod.IsHaarMeasure := Measure.pi.isHaarMeasure _
    let : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
    let coords := glPiEquiv n (fun _ : Fin l => F)
    let f (i : Fin l) (v : B.unipotentSubgroup F) : ℂ :=
      φ i (coords x i * (v : GeneralLinear n F) * coords y i)
    have heval (v : B.unipotentSubgroup (Fin l → F)) :
        splitTensor (fun i => (φ i : GeneralLinear n F → ℂ))
          (x * (v : GeneralLinear n (Fin l → F)) * y) = ∏ i, f i (e v i) := by
      change ∏ i, φ i (coords (x * v.val * y) i) = ∏ i, f i (e v i)
      simp only [map_mul, Pi.mul_apply]
      rfl
    calc
      _ = ∫ v, ∏ i, f i (e v i) ∂μ := integral_congr_ae (Eventually.of_forall heval)
      _ = ∫ w : Fin l → B.unipotentSubgroup F, ∏ i, f i (w i) ∂(μ.map e) :=
        (e.toHomeomorph.isClosedEmbedding.integral_map (μ := μ) (fun w => ∏ i, f i (w i))).symm
      _ = 0 := by
        rw [Measure.isMulLeftInvariant_eq_smul (μ.map e) νprod, integral_smul_nnreal_measure]
        change _ • (∫ w, ∏ i, f i (w i) ∂(Measure.pi fun _ : Fin l => ν)) = 0
        rw [integral_fintype_prod_eq_prod f]
        have h₀ : (∫ v, f i₀ v ∂ν) = 0 :=
          (hcusp B hB ν inferInstance).2 (coords x i₀) (coords y i₀)
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) h₀, smul_zero]

end Langlands.BaseChange
