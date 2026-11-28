import Langlands.Global.AdelicRegularizedFaceIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! # Fubini and regularization for an orthant partition by translated faces -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped Classical

set_option autoImplicit false

namespace Langlands.Global

variable {n : ℕ}

local notation "X" => (Fin n → ℝ)
local notation "Spectral" => (Fin n → ℂ)
local notation "Outside[" s "]" => ({a : Fin n // a ∉ s} → ℝ)

/-- A split base chart followed by a negative coordinate face. In the complementary
coordinates the base placement is the identity. The face directions use strict inequalities. -/
def orthantFaceCell (s : Set (Fin n)) (B : Set (Outside[s])) (b : Outside[s] → X) : Set X :=
  {x | (fun a : {a // a ∉ s} => x a.val) ∈ B ∧
    ∀ a : s, x a.val < b (fun j => x j.val) a.val}

/-- The density used in the ordinary coroot-coordinate cone integral. -/
private def coneKernel (p : MvPolynomial (Fin n) ℂ) (z : Spectral) (x : X) : ℂ :=
  Complex.exp (∑ a, z a * (x a : ℂ)) * p.eval (fun a => (x a : ℂ))

private def faceShear (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b) :
    Outside[s] × (s → ℝ) ≃ᵐ Outside[s] × (s → ℝ) where
  toFun v := (v.1, fun a => v.2 a + b v.1 a.val)
  invFun v := (v.1, fun a => v.2 a - b v.1 a.val)
  left_inv v := by simp
  right_inv v := by simp
  measurable_toFun := measurable_fst.prodMk (Measurable.of_eval fun (a : s) =>
    ((measurable_pi_apply a).comp measurable_snd).add
      ((measurable_pi_apply a.val).comp (hb.comp measurable_fst)))
  measurable_invFun := measurable_fst.prodMk (Measurable.of_eval fun (a : s) =>
    ((measurable_pi_apply a).comp measurable_snd).sub
      ((measurable_pi_apply a.val).comp (hb.comp measurable_fst)))

private theorem measurePreserving_faceShear (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b) :
    MeasurePreserving (faceShear s b hb) (volume.prod volume) (volume.prod volume) := by
  exact MeasurePreserving.skew_product (MeasurePreserving.id volume)
    (g := fun (y : Outside[s]) (u : s → ℝ) (a : s) => u a + b y a.val)
    ((faceShear s b hb).measurable.snd)
    (Eventually.of_forall fun y => (measurePreserving_add_right volume (fun (a : s) => b y a.val)).map_eq)

private def faceChart (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b) :
    Outside[s] × (s → ℝ) ≃ᵐ X :=
  (faceShear s b hb).trans <| MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ s)).symm

private theorem measurePreserving_faceChart (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b) :
    MeasurePreserving (faceChart s b hb) (volume.prod volume) volume := by
  have h := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ s)
  exact (h.symm _).comp (Measure.measurePreserving_swap.comp (measurePreserving_faceShear s b hb))

private theorem faceChart_inside (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b)
    (y : Outside[s]) (u : s → ℝ) (a : s) : faceChart s b hb (y, u) a.val = u a + b y a.val := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ s)
  exact congrArg (fun (v : (s → ℝ) × Outside[s]) => v.1 a) (e.apply_symm_apply (fun j => u j + b y j.val, y))

private theorem faceChart_outside (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b)
    (y : Outside[s]) (u : s → ℝ) (a : {a // a ∉ s}) : faceChart s b hb (y, u) a.val = y a := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ s)
  exact congrArg (fun (v : (s → ℝ) × Outside[s]) => v.2 a) (e.apply_symm_apply (fun j => u j + b y j.val, y))

private theorem preimage_orthantFaceCell (s : Set (Fin n)) (B : Set (Outside[s]))
    (b : Outside[s] → X) (hb : Measurable b) :
    faceChart s b hb ⁻¹' orthantFaceCell s B b = B ×ˢ (univ.pi fun _ : s => Iio (0 : ℝ)) := by
  ext ⟨y, u⟩
  change ((fun a : {a // a ∉ s} => faceChart s b hb (y, u) a.val) ∈ B ∧ _) ↔ _
  have hy : (fun a : {a // a ∉ s} => faceChart s b hb (y, u) a.val) = y :=
    funext (faceChart_outside s b hb y u)
  change ((fun a : {a // a ∉ s} => faceChart s b hb (y, u) a.val) ∈ B ∧
    ∀ a : s, faceChart s b hb (y, u) a.val < b (fun j => faceChart s b hb (y, u) j.val) a.val) ↔ _
  simp [hy, faceChart_inside]

private theorem faceChart_eq (s : Set (Fin n)) (b : Outside[s] → X) (hb : Measurable b)
    (hout : ∀ y (a : {a // a ∉ s}), b y a.val = y a) (y : Outside[s]) (u : s → ℝ) :
    faceChart s b hb (y, u) = fun a =>
      b y a + ∑ j ∈ Finset.univ.filter (fun j : s => j.val = a), u j := by
  funext a
  by_cases h : a ∈ s
  · let a' : s := ⟨a, h⟩
    have hfilter : Finset.univ.filter (fun j : s => j.val = a) = {a'} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Subtype.ext_iff, a']
    rw [hfilter, Finset.sum_singleton, faceChart_inside s b hb y u a', add_comm]
  · have hfilter : Finset.univ.filter (fun j : s => j.val = a) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun he => h (he ▸ j.property)
    rw [hfilter, Finset.sum_empty, add_zero, faceChart_outside s b hb y u ⟨a, h⟩]
    exact (hout y ⟨a, h⟩).symm

private theorem strict_orthant_ae_eq (s : Set (Fin n)) :
    (univ.pi fun _ : s => Iio (0 : ℝ)) =ᵐ[volume] (univ.pi fun _ : s => Iic (0 : ℝ)) := by
  have hne : ∀ᵐ u : s → ℝ ∂volume, ∀ a : s, u a ≠ 0 := by
    rw [ae_all_iff]
    exact fun a => Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) a 0
  filter_upwards [hne] with u hu
  simp only [mem_univ_pi, mem_Iio, mem_Iic]
  exact propext ⟨fun h a => (h a).le, fun h a => lt_of_le_of_ne (h a) (hu a)⟩

private theorem measurableSet_orthantFaceCell (s : Set (Fin n)) (B : Set (Outside[s]))
    (hB : MeasurableSet B) (b : Outside[s] → X) (hb : Measurable b) :
    MeasurableSet (orthantFaceCell s B b) := by
  let e := faceChart s b hb
  rw [← e.image_preimage (orthantFaceCell s B b), preimage_orthantFaceCell s B b hb]
  exact e.measurableEmbedding.measurableSet_image.mpr
    (hB.prod (MeasurableSet.univ_pi fun _ => measurableSet_Iio))

private theorem integral_orthantFaceCell (s : Set (Fin n)) (B : Set (Outside[s]))
    (b : Outside[s] → X) (hb : Measurable b)
    (hout : ∀ y (a : {a // a ∉ s}), b y a.val = y a) (p : MvPolynomial (Fin n) ℂ)
    (z : Spectral) (hB : MeasurableSet B) (hint : IntegrableOn (coneKernel p z) (orthantFaceCell s B b)) :
    (∫ x in orthantFaceCell s B b, coneKernel p z x) =
      ∫ y in B, affineFaceIntegral (Function.Embedding.subtype (· ∈ s)) (b y) p z := by
  let e := faceChart s b hb
  have he := measurePreserving_faceChart s b hb
  have hpre := preimage_orthantFaceCell s B b hb
  have hm := measurableSet_orthantFaceCell s B hB b hb
  have hι := ((he.restrict_preimage hm).integrable_comp_emb e.measurableEmbedding).mpr hint
  rw [hpre] at hι
  rw [← he.setIntegral_preimage_emb e.measurableEmbedding, hpre]
  change (∫ v in B ×ˢ (univ.pi fun _ : s => Iio (0 : ℝ)),
    (coneKernel p z ∘ e) v ∂volume.prod volume) = _
  rw [setIntegral_prod _ hι]
  apply integral_congr_ae
  filter_upwards with y
  rw [setIntegral_congr_set (strict_orthant_ae_eq s)]
  simp only [affineFaceIntegral, Function.Embedding.subtype_apply, Function.comp_def,
    faceChart_eq s b hb hout, coneKernel]
  rfl


private theorem preimage_translatedOrthant (t : X) :
    (MeasurableEquiv.addLeft t) ⁻¹' {x | ∀ a, x a ≤ t a} =
      univ.pi (fun _ => Iic (0 : ℝ)) := by
  ext u
  simp only [mem_preimage, MeasurableEquiv.coe_addLeft, mem_ofPred_eq,
    Pi.add_apply, mem_univ_pi, mem_Iic, add_le_iff_nonpos_right]

private theorem coneKernel_integrable (t : X) (p : MvPolynomial (Fin n) ℂ)
    (z : Spectral) (hz : ∀ a, 0 < (z a).re) :
    IntegrableOn (coneKernel p z) {x | ∀ a, x a ≤ t a} := by
  let A : Set X := {x | ∀ a, x a ≤ t a}
  let e := MeasurableEquiv.addLeft t
  have he : MeasurePreserving e volume volume := measurePreserving_add_left _ t
  have hA : MeasurableSet A := by
    rw [show A = univ.pi (fun a => Iic (t a)) from Set.ext fun _ => mem_univ_pi.symm]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Iic
  have hpre : e ⁻¹' A = univ.pi (fun _ => Iic (0 : ℝ)) :=
    preimage_translatedOrthant t
  unfold IntegrableOn
  rw [← (he.restrict_preimage hA).integrable_comp_emb e.measurableEmbedding, hpre]
  rw [volume_pi, Measure.restrict_pi_pi]
  let q := translatedFacePolynomial (Function.Embedding.refl (Fin n)) p t
  have hterm (u : X) : coneKernel p z (e u) =
      Complex.exp (∑ a, z a * (t a : ℂ)) *
        ∑ k ∈ q.support, q.coeff k * ∏ a, ((u a : ℂ) ^ k a * Complex.exp (z a * u a)) := by
    have hpoly : p.eval (fun a => ((t a + u a : ℝ) : ℂ)) = q.eval (fun a => (u a : ℂ)) := by
      simpa only [q, Function.Embedding.refl_apply, Finset.sum_filter, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Complex.ofReal_add] using
        (eval_translatedFacePolynomial (Function.Embedding.refl (Fin n)) p t u).symm
    simp only [coneKernel, e, MeasurableEquiv.coe_addLeft, Pi.add_apply, hpoly]
    simp only [Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add, mul_assoc]
    congr 1
    rw [MvPolynomial.eval_eq', Finset.mul_sum, Complex.exp_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.prod_mul_distrib]; ring
  simp only [Function.comp_def, hterm]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro k hk
  exact (Integrable.fintype_prod fun a => integrableOn_Iic_pow_mul_cexp (hz a) (k a)).const_mul _

/-- The pullback of Lebesgue measure to the split base. -/
def orthantFaceBaseMeasure (s : Set (Fin n)) (B : Set (Outside[s])) : Measure B :=
  (volume : Measure (Outside[s])).comap Subtype.val

/-- A finite partition of a translated negative orthant by coordinate faces over compact
complementary bases gives the corresponding sum of regularized face integrals. Each base
measure is Lebesgue measure in the complementary coordinates, restricted to that base. -/
def RegularizedOrthantPartitionIntegralStatement : Prop :=
  ∀ {m : ℕ} (s : Fin m → Set (Fin n)) (B : ∀ k, Set (Outside[s k]))
    (b : ∀ k, Outside[s k] → X) (t : X) (p : MvPolynomial (Fin n) ℂ),
    (∀ k, IsCompact (B k)) → (∀ k, Continuous (b k)) →
    (∀ k y (a : {a // a ∉ s k}), b k y a.val = y a) →
    Pairwise (Disjoint on fun k => orthantFaceCell (s k) (B k) (b k)) →
    {x | ∀ a, x a ≤ t a} = ⋃ k, orthantFaceCell (s k) (B k) (b k) →
    ∀ z : Spectral, (∀ a, z a ≠ 0) →
      Complex.exp (∑ a, z a * (t a : ℂ)) * negativeOrthantRegularizedIntegral z (polynomialShift t p) =
        ∑ k, regularizedAffineFaceIntegral (orthantFaceBaseMeasure (s k) (B k))
          (Function.Embedding.subtype (· ∈ s k)) (fun y : B k => b k y.val) p z

set_option maxHeartbeats 2100000 in
/-- Prove the ordinary identity by measure-preserving shear, product integration and finite
additivity, then continue it on the common nonzero-coordinate locus. -/
theorem regularizedOrthantPartitionIntegral : RegularizedOrthantPartitionIntegralStatement (n := n) := by
  intro m s B b t p hB hb hout hdis hcover
  let cell (k : Fin m) := orthantFaceCell (s k) (B k) (b k)
  let A : Set X := {x | ∀ a, x a ≤ t a}
  have hcell (k : Fin m) : MeasurableSet (cell k) :=
    measurableSet_orthantFaceCell _ _ (hB k).measurableSet _ (hb k).measurable
  let i (k : Fin m) : (s k : Type) ↪ Fin n := Function.Embedding.subtype (· ∈ s k)
  let (k : Fin m) : CompactSpace (B k) := isCompact_iff_compactSpace.mp (hB k)
  let (k : Fin m) : IsFiniteMeasure (orthantFaceBaseMeasure (s k) (B k)) := by
    constructor
    rw [orthantFaceBaseMeasure, comap_subtype_coe_apply (hB k).measurableSet, image_univ, Subtype.range_coe]
    exact (hB k).measure_lt_top
  apply regularizedAffineFaceRecombination (fun k => (s k : Type)) (fun k => (B k : Type))
    (fun k => (orthantFaceBaseMeasure (s k) (B k))) i (fun k y => b k y.val) t p
    (fun k => (hb k).comp continuous_subtype_val)
  intro z hz
  have hint := coneKernel_integrable t p z hz
  have hs (k : Fin m) : cell k ⊆ A := by
    rw [show A = ⋃ k, cell k from hcover]
    exact subset_iUnion cell k
  have hsum : (∫ x in A, coneKernel p z x) = ∑ k, ∫ x in cell k, coneKernel p z x := by
    rw [show A = ⋃ k, cell k from hcover]
    exact integral_iUnion_fintype hcell hdis fun k => hint.mono_set (hs k)
  let e := MeasurableEquiv.addLeft t
  have he : MeasurePreserving e volume volume := measurePreserving_add_left _ t
  have ha : affineFaceIntegral (Function.Embedding.refl (Fin n)) t p z =
      ∫ x in A, coneKernel p z x := by
    rw [← he.setIntegral_preimage_emb e.measurableEmbedding]
    have hpre : e ⁻¹' A = univ.pi (fun _ => Iic (0 : ℝ)) :=
      preimage_translatedOrthant t
    rw [hpre]
    simp only [affineFaceIntegral, coneKernel, e, MeasurableEquiv.coe_addLeft, Pi.add_apply,
      Function.Embedding.refl_apply, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [ha, hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_orthantFaceCell (s k) (B k) (b k) (hb k).measurable (hout k) p z
    (hB k).measurableSet (hint.mono_set (hs k))]
  exact (integral_subtype_comap (hB k).measurableSet (fun y => affineFaceIntegral (i k) (b k y) p z)).symm

end Langlands.Global
