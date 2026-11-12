import Langlands.Representation.Hecke.CompactTensorGroupBalance
import Langlands.Group.LeftQuotient
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Finite source-coset expansions in the original Hecke tensor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MulOpposite Classical
open scoped TensorProduct

namespace Langlands.Hecke

open HarmonicAnalysis Langlands.Algebra

universe uG uH v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]

/-- The actual Hecke test `1_(K*g)`, without normalizing either Haar mass. -/
def HeckeAlgebra.rightCosetIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) : HeckeAlgebra μG :=
  (HeckeAlgebra.toTestFunction μG).symm
    (TestFunction.rightTranslate g⁻¹ (TestFunction.subgroupIndicator K hK))

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [μG.IsHaarMeasure] in
@[simp] theorem HeckeAlgebra.rightCosetIndicator_apply (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g x : G) :
    HeckeAlgebra.rightCosetIndicator μG K hK g x =
      (K : Set G).indicator (fun _ => (1 : ℂ)) (x * g⁻¹) := rfl

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [μG.IsHaarMeasure] in
/-- A coset indicator is the Kronecker function on the left quotient. -/
theorem HeckeAlgebra.rightCosetIndicator_quotient (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (q : Induction.LeftQuotient K.toSubgroup) (x : G) :
    HeckeAlgebra.rightCosetIndicator μG K hK q.out x =
      if Induction.quotientMap K.toSubgroup x = q then 1 else 0 := by
  classical
  have he : Induction.quotientMap K.toSubgroup x = q ↔ x * q.out⁻¹ ∈ K := by
    constructor
    · intro hq
      exact QuotientGroup.rightRel_apply.mp
        (Quotient.exact ((Quotient.out_eq' q).trans hq.symm))
    · intro hx
      have hq : Induction.quotientMap K.toSubgroup q.out =
          Induction.quotientMap K.toSubgroup x :=
        Quotient.sound (QuotientGroup.rightRel_apply.mpr hx)
      exact hq.symm.trans (Quotient.out_eq' q)
  simp only [HeckeAlgebra.rightCosetIndicator_apply, Set.indicator_apply]
  simp only [he]
  rfl

omit [T2Space G] [NonarchimedeanGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [μG.IsHaarMeasure] in
/-- A left-invariant test is recovered at each point from its quotient representative. -/
theorem leftInvariant_eq_quotient_out (K : OpenSubgroup G) (T : HeckeAlgebra μG)
    (hT : ∀ k : K, ∀ x, T ((k : G) * x) = T x) (x : G) :
    T (Induction.quotientMap K.toSubgroup x).out = T x := by
  let q := Induction.quotientMap K.toSubgroup x
  have hk : q.out * x⁻¹ ∈ K :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq' q).symm)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hT ⟨q.out * x⁻¹, hk⟩ x

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [μG.IsHaarMeasure] in
/-- Compact support supplies finitely many left cosets covering the nonzero test. -/
theorem exists_finset_leftCoset_support (K : OpenSubgroup G) (T : HeckeAlgebra μG) :
    ∃ s : Finset (Induction.LeftQuotient K.toSubgroup),
      ∀ x, T x ≠ 0 → Induction.quotientMap K.toSubgroup x ∈ s := by
  classical
  obtain ⟨t, ht⟩ := (TestFunction.isCompact_support (HeckeAlgebra.toTestFunction μG T)
    ).elim_finite_subcover
    (fun i : G => (fun k => k * i) '' (K : Set G))
    (fun i => isOpenMap_mul_right i _ K.isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, 1, K.one_mem, one_mul x⟩)
  refine ⟨t.image (Induction.quotientMap K.toSubgroup), ?_⟩
  intro x hx
  have hcover := ht hx
  simp only [Set.mem_iUnion] at hcover
  obtain ⟨i, hi, k, hk, rfl⟩ := hcover
  apply Finset.mem_image.mpr
  refine ⟨i, hi, ?_⟩
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  change k ∈ K.toSubgroup at hk
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hk

omit [T2Space G] [LocallyCompactSpace G] in
/-- Every left-`K`-invariant test is a finite sum of actual coset indicators,
with coefficients given by its own values. -/
theorem finite_leftCoset_expansion (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (T : HeckeAlgebra μG) (hT : ∀ k : K, ∀ x, T ((k : G) * x) = T x) :
    ∃ s : Finset (Induction.LeftQuotient K.toSubgroup),
      T = ∑ q ∈ s, T q.out • HeckeAlgebra.rightCosetIndicator μG K hK q.out := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_leftCoset_support μG K T
  refine ⟨s, ?_⟩
  apply HeckeAlgebra.ext
  intro x
  let ev : HeckeAlgebra μG →ₗ[ℂ] ℂ :=
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change T x = ev (∑ q ∈ s, T q.out • HeckeAlgebra.rightCosetIndicator μG K hK q.out)
  rw [map_sum]
  change T x = ∑ q ∈ s, T q.out * HeckeAlgebra.rightCosetIndicator μG K hK q.out x
  simp_rw [HeckeAlgebra.rightCosetIndicator_quotient]
  let q := Induction.quotientMap K.toSubgroup x
  change T x = ∑ r ∈ s, T r.out * (if q = r then 1 else 0)
  by_cases hq : q ∈ s
  · rw [Finset.sum_eq_single q]
    · simpa only [ite_true, mul_one] using (leftInvariant_eq_quotient_out μG K T hT x).symm
    · intro r _ hr
      simp only [ite_eq_right (Ne.symm hr), mul_zero]
    · exact fun hn => absurd hq hn
  · have hz : T x = 0 := not_not.mp (mt (hs x) hq)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hne : q ≠ r := fun he => hq (he.symm ▸ hr)
    simp only [ite_eq_right hne, mul_zero]

namespace Homomorphism

variable {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- Scalar multiplication of the subgroup test is scalar multiplication of
the original right action. -/
theorem rightModule_smul_test (c : ℂ) (a : HeckeAlgebra μH) (T : HeckeAlgebra μG) :
    letI := rightModule μG μH φ hφ
    op (c • a) • T = c • (op a • T) := by
  let _ := rightModule μG μH φ hφ
  ext x
  change (op (c • a) • T) x = c * (op a • T) x
  rw [rightModule_integral, rightModule_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with h
  change haarScale (φ h) * (c * a h) * T (x * (φ h)⁻¹) = _
  ring

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- Complex scalars move between the original integer tensor factors as a
consequence of right nondegeneracy, without imposing a new relation. -/
theorem tensor_scalar_balanced (c : ℂ) (T : HeckeAlgebra μG) (w : V) :
    letI := rightModule μG μH φ hφ
    letI := heckeNonUnitalModule μH ρ hρ
    NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V (c • T) w =
      NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T (c • w) := by
  let _ := rightModule μG μH φ hφ
  let _ := heckeNonUnitalModule μH ρ hρ
  obtain ⟨e, he⟩ := rightModule_isNondegenerate μG μH φ hφ T
  let a : HeckeAlgebra μH := unop (e : (HeckeAlgebra μH)ᵐᵒᵖ)
  have ha : op a • T = T := he
  have hcw : (c • a) • w = a • (c • w) := by
    change integratedAction μH ρ hρ
        (c • HeckeAlgebra.toTestFunction μH a) w =
      integratedAction μH ρ hρ (HeckeAlgebra.toTestFunction μH a) (c • w)
    simp only [map_smul, LinearMap.smul_apply]
  calc
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
        (op (c • a) • T) w := by rw [rightModule_smul_test, ha]
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T
        ((c • a) • w) := NonUnitalModuleTensor.tmul_balanced _ _ _ _ _ _
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T
        (a • (c • w)) := by rw [hcw]
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
        (op a • T) (c • w) := (NonUnitalModuleTensor.tmul_balanced _ _ _ _ _ _).symm
    _ = _ := by rw [ha]

/-- Every tensor has a finite common-compact-open coset-indicator normal form.
Only finitely many cosets occur, even when both quotient spaces are infinite. -/
theorem tensor_finite_coset_normal_form :
    letI := rightModule μG μH φ hφ
    letI := heckeNonUnitalModule μH ρ hρ
    ∀ t : NonUnitalModuleTensor.Tensor (HeckeAlgebra μH) (HeckeAlgebra μG) V,
      ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
        (n : ℕ) (s : Fin n → Finset (Induction.LeftQuotient K.toSubgroup))
        (w : Fin n → Induction.LeftQuotient K.toSubgroup → V),
        t = ∑ i : Fin n, ∑ q ∈ s i,
          NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
            (HeckeAlgebra.rightCosetIndicator μG K hK q.out) (w i q) := by
  let _ := rightModule μG μH φ hφ
  let _ := heckeNonUnitalModule μH ρ hρ
  intro t
  obtain ⟨q, rfl⟩ := NonUnitalModuleTensor.projection_surjective
    (HeckeAlgebra μH) (HeckeAlgebra μG) V t
  obtain ⟨n, T, w, hq⟩ := TensorProduct.exists_sum_tmul_eq q
  obtain ⟨K, _, hK, hfix⟩ := TestFunction.commonCompactOpenBiInvariance G
    (Finset.univ.image (fun i : Fin n => HeckeAlgebra.toTestFunction μG (T i))) ⊤
  have hT (i : Fin n) : ∀ k : K, ∀ x, T i ((k : G) * x) = T i x :=
    (hfix (HeckeAlgebra.toTestFunction μG (T i))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).1
  choose s hs using fun i => finite_leftCoset_expansion μG K hK (T i) (hT i)
  refine ⟨K, hK, n, s, fun i r => T i r.out • w i, ?_⟩
  rw [hq, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  let b : HeckeAlgebra μG →+
      NonUnitalModuleTensor.Tensor (HeckeAlgebra μH) (HeckeAlgebra μG) V :=
    { toFun := fun a => NonUnitalModuleTensor.tmul
        (HeckeAlgebra μH) (HeckeAlgebra μG) V a (w i)
      map_zero' := NonUnitalModuleTensor.zero_tmul _ _ _ _
      map_add' := fun a a' => NonUnitalModuleTensor.add_tmul _ _ _ a a' (w i) }
  change b (T i) = _
  rw [hs i, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact tensor_scalar_balanced μG μH φ hφ ρ hρ (T i r.out)
    (HeckeAlgebra.rightCosetIndicator μG K hK r.out) (w i)

end Homomorphism

end Langlands.Hecke
