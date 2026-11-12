import Langlands.GroupScheme.Quaternionic.Involution
import Langlands.Algebra.ReducedCharpolyDivision
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic.NoncommRing

/-! # Conjugation obtained from an alternating quaternionic unit -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open Polynomial
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)

/-- An anti-involution of a division algebra preserves inversion. -/
@[simp] theorem map_inv (a : D) : σ a⁻¹ = (σ a)⁻¹ := by
  by_cases ha : a = 0
  · subst a
    simp
  · apply eq_inv_of_mul_eq_one_left
    rw [← σ.map_mul, mul_inv_cancel₀ ha, σ.map_one]

/-- Every alternating element is anti-selfadjoint, also in characteristic two. -/
theorem map_eq_neg_of_mem_alternating {l : D} (hl : l ∈ σ.alternatingSubspace) :
    σ l = -l := by
  obtain ⟨a, rfl⟩ := σ.mem_alternatingSubspace.mp hl
  simp [neg_sub]

/-- Twist the involution by an invertible anti-selfadjoint element. -/
def alternatingTwist (l : Dˣ) (hl : σ (l : D) = -(l : D)) :
    Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D where
  toLinearMap :=
    { toFun a := (l : D) * σ a * ((l : D)⁻¹)
      map_add' a b := by simp [mul_add, add_mul]
      map_smul' c a := by simp }
  map_one' := by simp
  map_mul' a b := by simp [mul_assoc]
  involutive' a := by simp [map_inv, hl, mul_assoc]

@[simp] theorem alternatingTwist_apply (l : Dˣ) (hl : σ (l : D) = -(l : D)) (a : D) :
    σ.alternatingTwist l hl a = (l : D) * σ a * (l : D)⁻¹ := rfl

private theorem exists_alternatingNorm
    (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace) (a : D) :
    ∃ c : K, algebraMap K D c * (l : D) = a * (l : D) * σ a := by
  have hmem : a * (l : D) * σ a ∈ σ.alternatingSubspace := by
    obtain ⟨b, hb⟩ := σ.mem_alternatingSubspace.mp hl
    apply σ.mem_alternatingSubspace.mpr
    refine ⟨a * b * σ a, ?_⟩
    rw [← hb]
    simp only [map_mul, apply_apply]
    noncomm_ring
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline
    (show (⟨(l : D), hl⟩ : σ.alternatingSubspace) ≠ 0 from
      fun h => l.ne_zero (congrArg Subtype.val h))
    (⟨a * (l : D) * σ a, hmem⟩ : σ.alternatingSubspace)
  refine ⟨c, ?_⟩
  simpa only [Submodule.coe_smul_of_tower, Algebra.smul_def] using congrArg Subtype.val hc

/-- The scalar by which a sandwich scales the one-dimensional alternating line. -/
def alternatingNorm (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace) (a : D) : K :=
  Classical.choose (σ.exists_alternatingNorm hline l hl a)

theorem alternatingNorm_sandwich
    (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace) (a : D) :
    algebraMap K D (σ.alternatingNorm hline l hl a) * (l : D) =
      a * (l : D) * σ a :=
  Classical.choose_spec (σ.exists_alternatingNorm hline l hl a)

/-- The twisted involution gives a scalar-valued conjugate product. -/
theorem alternatingNorm_spec
    (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace) (a : D) :
    algebraMap K D (σ.alternatingNorm hline l hl a) =
      a * σ.alternatingTwist l (σ.map_eq_neg_of_mem_alternating hl) a := by
  have h := congrArg (fun z : D => z * (l : D)⁻¹)
    (σ.alternatingNorm_sandwich hline l hl a)
  simpa [mul_assoc] using h

/-- The scalar trace associated with the one-dimensional alternating line. -/
def alternatingTrace (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace) (a : D) : K :=
  σ.alternatingNorm hline l hl (1 + a) - 1 - σ.alternatingNorm hline l hl a

/-- The scalar trace is the sum of an element and its twisted conjugate. -/
theorem alternatingTrace_spec
    (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace) (a : D) :
    algebraMap K D (σ.alternatingTrace hline l hl a) =
      a + σ.alternatingTwist l (σ.map_eq_neg_of_mem_alternating hl) a := by
  simp only [alternatingTrace, _root_.map_sub, _root_.map_one, alternatingNorm_spec,
    FirstKindInvolution.map_add, FirstKindInvolution.map_one]
  noncomm_ring

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : Langlands.GroupScheme.Quaternionic.FirstKindInvolution K D)

/-- The scalar sandwich norm is the actual reduced norm in reduced degree two. -/
theorem alternatingNorm_eq_reducedNorm
    (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace)
    (hdegree : Langlands.CentralSimple.reducedDegree K D = 2) (a : D) :
    σ.alternatingNorm hline l hl a =
      Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a) := by
  by_cases ha : a ∈ Set.range (algebraMap K D)
  · obtain ⟨c, rfl⟩ := ha
    have hn : σ.alternatingNorm hline l hl (algebraMap K D c) = c ^ 2 := by
      apply FaithfulSMul.algebraMap_injective K D
      rw [σ.alternatingNorm_spec,
        (σ.alternatingTwist l (σ.map_eq_neg_of_mem_alternating hl)).map_algebraMap]
      simp [pow_two]
    rw [hn]
    have ht : (1 : K) ⊗ₜ[K] algebraMap K D c = c ⊗ₜ[K] (1 : D) := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
      simp
    rw [ht, Langlands.CentralSimple.reducedNorm_scalar, hdegree]
  · let bar := σ.alternatingTwist l (σ.map_eq_neg_of_mem_alternating hl)
    let n := σ.alternatingNorm hline l hl a
    let t := σ.alternatingTrace hline l hl a
    let c₁ := (Langlands.CentralSimple.reducedCharpoly K D a).coeff 1
    let c₀ := Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a)
    have hnorm : algebraMap K D n = a * bar a := σ.alternatingNorm_spec hline l hl a
    have htrace : algebraMap K D t = a + bar a := σ.alternatingTrace_spec hline l hl a
    have hpoly : a ^ 2 + algebraMap K D c₁ * a + algebraMap K D c₀ = 0 := by
      have h := Langlands.CentralDivision.aeval_reducedCharpoly K D a
      rw [Langlands.CentralSimple.reducedCharpoly_eq_quadratic K D hdegree a] at h
      simpa only [_root_.map_add, _root_.map_mul, _root_.map_pow,
        Polynomial.aeval_X, Polynomial.aeval_C] using h
    have hprod : algebraMap K D c₁ * a + a * a = -algebraMap K D c₀ := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [pow_two, add_comm, add_left_comm, add_assoc] using hpoly
    have hdiff : algebraMap K D (c₁ + t) * a = algebraMap K D (n - c₀) := by
      rw [_root_.map_add, add_mul, Algebra.commutes t a, htrace,
        mul_add, ← hnorm, ← add_assoc, hprod]
      simp [sub_eq_add_neg, add_comm]
    have hco : c₁ + t = 0 := by
      by_contra hco
      apply ha
      refine ⟨(c₁ + t)⁻¹ * (n - c₀), ?_⟩
      have hcoeff : algebraMap K D (c₁ + t) ≠ 0 := by
        intro hz
        apply hco
        apply FaithfulSMul.algebraMap_injective K D
        simpa using hz
      apply mul_left_cancel₀ hcoeff
      calc
        algebraMap K D (c₁ + t) *
            algebraMap K D ((c₁ + t)⁻¹ * (n - c₀)) =
            algebraMap K D (n - c₀) := by
          rw [← _root_.map_mul, ← mul_assoc, mul_inv_cancel₀ hco, one_mul]
        _ = algebraMap K D (c₁ + t) * a := hdiff.symm
    have hzero : n - c₀ = 0 := by
      apply FaithfulSMul.algebraMap_injective K D
      simpa [hco] using hdiff.symm
    exact sub_eq_zero.mp hzero

/-- The alternating line transforms by the canonical quaternionic reduced norm. -/
theorem reducedNorm_sandwich_alternating
    (hline : Module.finrank K σ.alternatingSubspace = 1) (l : Dˣ)
    (hl : (l : D) ∈ σ.alternatingSubspace)
    (hdegree : Langlands.CentralSimple.reducedDegree K D = 2) (a : D) :
    a * (l : D) * σ a =
      algebraMap K D (Langlands.CentralSimple.reducedNorm K D K (1 ⊗ₜ[K] a)) * (l : D) := by
  rw [← σ.alternatingNorm_eq_reducedNorm hline l hl hdegree]
  exact (σ.alternatingNorm_sandwich hline l hl a).symm

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
