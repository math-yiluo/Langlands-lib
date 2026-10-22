import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

/-! # Topological and algebraic properties of the concrete multiplicative spectrum -/

universe u v

namespace Langlands.Analytic.BanachSpectrum

variable {A : Type u} [NormedCommRing A]

theorem evaluation_injective :
    Function.Injective (fun x : BanachSpectrum A => (x : A → ℝ)) :=
  fun _ _ h => ext (congrFun h)

theorem evaluation_isEmbedding :
    Topology.IsEmbedding (fun x : BanachSpectrum A => (x : A → ℝ)) :=
  evaluation_injective.isEmbedding_induced

instance : T2Space (BanachSpectrum A) :=
  evaluation_isEmbedding.t2Space

private def conditions (f : A → ℝ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧ (∀ a b, f (a * b) = f a * f b) ∧
  (∀ a b, f (a + b) ≤ f a + f b) ∧ (∀ a, f (-a) = f a) ∧
  (∀ a, 0 ≤ f a) ∧ ∀ a, f a ≤ ‖a‖

private theorem conditions_iff (f : A → ℝ) :
    conditions f ↔ f ∈ Set.range (fun x : BanachSpectrum A => (x : A → ℝ)) := by
  constructor
  · rintro ⟨h0, h1, hmul, hadd, hneg, _, hbound⟩
    let x : BanachSpectrum A :=
      { toFun := f
        map_zero' := h0
        map_one' := h1
        map_mul' := hmul
        add_le' := hadd
        neg' := hneg
        le_norm := hbound }
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨map_zero x.toMulRingSeminorm, map_one x.toMulRingSeminorm,
      map_mul x.toMulRingSeminorm, map_add_le_add x.toMulRingSeminorm,
      map_neg_eq_map x.toMulRingSeminorm, apply_nonneg x.toMulRingSeminorm,
      x.le_norm⟩

theorem isClosed_range_evaluation :
    IsClosed (Set.range (fun x : BanachSpectrum A => (x : A → ℝ))) := by
  have hc : IsClosed {f : A → ℝ | conditions f} := by
    simp only [conditions, Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_eq (continuous_apply 0) continuous_const).inter
      ((isClosed_eq (continuous_apply 1) continuous_const).inter
      ((isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (continuous_apply (a * b))
          ((continuous_apply a).mul (continuous_apply b))).inter
      ((isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_le (continuous_apply (a + b))
          ((continuous_apply a).add (continuous_apply b))).inter
      ((isClosed_iInter fun a =>
        isClosed_eq (continuous_apply (-a)) (continuous_apply a)).inter
      ((isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)).inter
       (isClosed_iInter fun a => isClosed_le (continuous_apply a) continuous_const))))))
  convert hc using 1
  ext f
  exact (conditions_iff f).symm

theorem isCompact_range_evaluation :
    IsCompact (Set.range (fun x : BanachSpectrum A => (x : A → ℝ))) := by
  apply (isCompact_univ_pi fun a : A => isCompact_Icc (a := (0 : ℝ)) (b := ‖a‖)).of_isClosed_subset
    isClosed_range_evaluation
  rintro f ⟨x, rfl⟩ a _
  exact ⟨apply_nonneg x.toMulRingSeminorm a, x.le_norm a⟩

instance : CompactSpace (BanachSpectrum A) where
  isCompact_univ := evaluation_isEmbedding.isCompact_iff.mpr
    (by simpa only [Set.image_univ] using isCompact_range_evaluation (A := A))

theorem kernel_isPrime (x : BanachSpectrum A) : (kernel x).IsPrime := by
  constructor
  · intro h
    have h1 : (1 : A) ∈ kernel x := by rw [h]; trivial
    have heq : x.toMulRingSeminorm 1 = 0 := h1
    simp at heq
  · intro a b hab
    change x.toMulRingSeminorm (a * b) = 0 at hab
    rw [map_mul, mul_eq_zero] at hab
    exact hab

theorem field_apply {K : Type u} [NormedField K] (x : BanachSpectrum K) (a : K) :
    x a = ‖a‖ := by
  apply le_antisymm (x.le_norm a)
  by_cases ha : a = 0
  · subst a
    simp only [norm_zero]
    exact apply_nonneg x.toMulRingSeminorm 0
  have h : 1 ≤ x a * ‖a‖⁻¹ := by
    calc
      1 = x.toMulRingSeminorm a * x.toMulRingSeminorm a⁻¹ := by
        rw [← map_mul, mul_inv_cancel₀ ha, map_one]
      _ ≤ x a * ‖a⁻¹‖ :=
        mul_le_mul_of_nonneg_left (x.le_norm a⁻¹) (apply_nonneg x.toMulRingSeminorm a)
      _ = x a * ‖a‖⁻¹ := by rw [norm_inv]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have h' : (1 : ℝ) * ‖a‖ ≤ x a :=
    (le_div_iff₀ ha').mp (by simpa only [div_eq_mul_inv] using h)
  simpa only [one_mul] using h'

instance {K : Type u} [NormedField K] : Subsingleton (BanachSpectrum K) :=
  ⟨fun x y => ext fun a => (field_apply x a).trans (field_apply y a).symm⟩

theorem algebraMap_apply {K : Type v} [NormedField K] [NormedAlgebra K A]
    (x : BanachSpectrum A) (c : K) : x (algebraMap K A c) = ‖c‖ :=
  field_apply (comap (BoundedRingHom.scalarHom K A) x) c

theorem comap_id (x : BanachSpectrum A) : comap (BoundedRingHom.id A) x = x :=
  ext fun _ => rfl

theorem comap_comp {B C : Type*} [NormedCommRing B] [NormedCommRing C]
    (f : BoundedRingHom A B) (g : BoundedRingHom B C) (x : BanachSpectrum C) :
    comap (g.comp f) x = comap f (comap g x) :=
  ext fun _ => rfl

theorem preimage_laurentLocus {B : Type v} [NormedCommRing B] (φ : BoundedRingHom A B)
    {ι κ : Type*} (f : ι → A) (r : ι → ℝ) (g : κ → A) (s : κ → ℝ) :
    comap φ ⁻¹' laurentLocus f r g s = laurentLocus (φ ∘ f) r (φ ∘ g) s :=
  rfl

theorem isClosed_laurentLocus {ι κ : Type*} (f : ι → A) (r : ι → ℝ)
    (g : κ → A) (s : κ → ℝ) : IsClosed (laurentLocus f r g s) := by
  simp only [laurentLocus, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le (evaluation (f i)).continuous continuous_const).inter
    (isClosed_iInter fun j => isClosed_le continuous_const (evaluation (g j)).continuous)

theorem isCompact_laurentLocus {ι κ : Type*} (f : ι → A) (r : ι → ℝ)
    (g : κ → A) (s : κ → ℝ) : IsCompact (laurentLocus f r g s) :=
  (isClosed_laurentLocus f r g s).isCompact

end Langlands.Analytic.BanachSpectrum
