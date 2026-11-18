import Langlands.GroupScheme.Lie.NonaffineKernelConjugation
import Langlands.GroupScheme.Lie.NonaffineKernelMap

/-! # Actual square-zero kernel cocycles for homomorphism deformations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie.NonaffineKernel

open Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A] (J : Ideal A) [Fact (SqZero J)]
variable {P : Type u} [Group P]

/-- Any map whose reduction is a homomorphism acts on the actual square-zero
kernel by linear automorphisms, even when the map itself is not a homomorphism. -/
def reductionLiftAction (s : P → AffinePoints G A)
    (s₀ : P →* AffinePoints G (A ⧸ J))
    (hs : ∀ h, reduction G J (s h) = s₀ h) :
    P →* (Additive (kernel G J) ≃ₗ[A] Additive (kernel G J)) where
  toFun h := kernelConjugationAut G J (s h)
  map_one' := by
    change kernelConjugationAut G J (s 1) = 1
    rw [kernelConjugationAut_eq_of_reduction_eq G J (s 1) 1
      (by rw [hs, map_one, map_one]), map_one]
  map_mul' h k := by
    rw [← map_mul]
    apply kernelConjugationAut_eq_of_reduction_eq
    simp only [map_mul, hs]

@[simp]
theorem reductionLiftAction_val (s : P → AffinePoints G A)
    (s₀ : P →* AffinePoints G (A ⧸ J)) (hs : ∀ h, reduction G J (s h) = s₀ h)
    (h : P) (x : Additive (kernel G J)) :
    (reductionLiftAction G J s s₀ hs h x).toMul.val = s h * x.toMul.val * (s h)⁻¹ :=
  kernelConjugationAut_val G J (s h) x

/-- The multiplicativity defect is an element of the actual reduction kernel. -/
def kernelDefect (s : P → AffinePoints G A)
    (s₀ : P →* AffinePoints G (A ⧸ J))
    (hs : ∀ h, reduction G J (s h) = s₀ h) (h k : P) :
    Additive (kernel G J) :=
  Additive.ofMul ⟨s h * s k * (s (h * k))⁻¹, by
    change reduction G J (s h * s k * (s (h * k))⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hs, hs, hs, map_mul, mul_inv_cancel]⟩

omit [Fact (SqZero J)] in
@[simp]
theorem kernelDefect_val (s : P → AffinePoints G A)
    (s₀ : P →* AffinePoints G (A ⧸ J)) (hs : ∀ h, reduction G J (s h) = s₀ h)
    (h k : P) :
    (kernelDefect G J s s₀ hs h k).toMul.val = s h * s k * (s (h * k))⁻¹ := rfl

/-- Associativity gives the actual additive two-cocycle equation for the
linear action induced by the reducing homomorphism. -/
theorem kernelDefect_cocycle (s : P → AffinePoints G A)
    (s₀ : P →* AffinePoints G (A ⧸ J)) (hs : ∀ h, reduction G J (s h) = s₀ h)
    (h k l : P) :
    kernelDefect G J s s₀ hs h k + kernelDefect G J s s₀ hs (h * k) l =
      reductionLiftAction G J s s₀ hs h (kernelDefect G J s s₀ hs k l) +
        kernelDefect G J s s₀ hs h (k * l) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [toMul_add, Subgroup.coe_mul, kernelDefect_val, reductionLiftAction_val]
  rw [mul_assoc h k l]
  group

/-- An additive two-coboundary equation is precisely the ambient group-valued
equation needed to correct the original map. -/
theorem kernelDefect_correctionEquation (s : P → AffinePoints G A)
    (s₀ : P →* AffinePoints G (A ⧸ J)) (hs : ∀ h, reduction G J (s h) = s₀ h)
    (b : P → Additive (kernel G J))
    (hb : ∀ h k, kernelDefect G J s s₀ hs h k + b (h * k) =
      reductionLiftAction G J s s₀ hs h (b k) + b h) (h k : P) :
    (s h * s k * (s (h * k))⁻¹) * (b (h * k)).toMul.val =
      (s h * (b k).toMul.val * (s h)⁻¹) * (b h).toMul.val := by
  simpa only [toMul_add, Subgroup.coe_mul, kernelDefect_val, reductionLiftAction_val] using
    congrArg (fun x : Additive (kernel G J) => x.toMul.val) (hb h k)

/-- The difference between homomorphisms with equal reductions lies in the
actual square-zero reduction kernel. -/
def kernelDifference (f f' : P →* AffinePoints G A)
    (hf : ∀ h, reduction G J (f h) = reduction G J (f' h)) (h : P) :
    Additive (kernel G J) :=
  Additive.ofMul ⟨f' h * (f h)⁻¹, by
    change reduction G J (f' h * (f h)⁻¹) = 1
    rw [map_mul, map_inv, hf, mul_inv_cancel]⟩

omit [Fact (SqZero J)] in
@[simp]
theorem kernelDifference_val (f f' : P →* AffinePoints G A)
    (hf : ∀ h, reduction G J (f h) = reduction G J (f' h)) (h : P) :
    (kernelDifference G J f f' hf h).toMul.val = f' h * (f h)⁻¹ := rfl

/-- The difference satisfies the additive one-cocycle equation for conjugation
through the first homomorphism. -/
theorem kernelDifference_cocycle (f f' : P →* AffinePoints G A)
    (hf : ∀ h, reduction G J (f h) = reduction G J (f' h)) (h k : P) :
    kernelDifference G J f f' hf (h * k) =
      kernelDifference G J f f' hf h +
        kernelConjugationAut G J (f h) (kernelDifference G J f f' hf k) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [toMul_add, Subgroup.coe_mul, kernelDifference_val, kernelConjugationAut_val]
  rw [map_mul, map_mul]
  group

/-- An actual one-coboundary primitive gives conjugacy by its inverse, an
element of the actual reduction kernel. -/
theorem kernelDifference_conjugacy (f f' : P →* AffinePoints G A)
    (hf : ∀ h, reduction G J (f h) = reduction G J (f' h))
    (m : Additive (kernel G J))
    (hm : ∀ h, kernelDifference G J f f' hf h =
      kernelConjugationAut G J (f h) m - m) (h : P) :
    f' h = m.toMul.val⁻¹ * f h * m.toMul.val := by
  have hh : kernelDifference G J f f' hf h =
      -m + kernelConjugationAut G J (f h) m := by
    rw [hm, sub_eq_add_neg, add_comm]
  have he := congrArg (fun x : Additive (kernel G J) => x.toMul.val) hh
  simp only [toMul_add, toMul_neg, Subgroup.coe_mul, Subgroup.coe_inv,
    kernelDifference_val, kernelConjugationAut_val] at he
  calc
    f' h = (f' h * (f h)⁻¹) * f h := by group
    _ = (m.toMul.val⁻¹ * (f h * m.toMul.val * (f h)⁻¹)) * f h := by rw [he]
    _ = m.toMul.val⁻¹ * f h * m.toMul.val := by group

section Naturality

variable {B : Type u} [CommRing B] [Algebra R B]
variable (q : A →ₐ[R] B) {J' : Ideal B} [Fact (SqZero J')]
variable (hJ : J.map q ≤ J')

omit [Fact (SqZero J)] [Fact (SqZero J')] in
/-- Kernel coefficient change retains the actual map on underlying points. -/
@[simp]
theorem kernelMapAdd_val (x : Additive (kernel G J)) :
    (kernelMapAdd G J q hJ x).toMul.val = affineMap G q x.toMul.val := rfl

/-- Actual linear conjugation commutes with every compatible coefficient map. -/
theorem kernelMapAdd_conjugation (g : AffinePoints G A) (x : Additive (kernel G J)) :
    kernelMapAdd G J q hJ (kernelConjugationAut G J g x) =
      kernelConjugationAut G J' (affineMap G q g) (kernelMapAdd G J q hJ x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [kernelMapAdd_val, kernelConjugationAut_val, map_mul, map_inv]

/-- A map reducing to a homomorphism gives compatible kernel actions whenever
its point values commute with coefficient change. -/
theorem reductionLiftAction_naturality
    (s : P → AffinePoints G A) (s' : P → AffinePoints G B)
    (s₀ : P →* AffinePoints G (A ⧸ J)) (s₀' : P →* AffinePoints G (B ⧸ J'))
    (hs : ∀ h, reduction G J (s h) = s₀ h)
    (hs' : ∀ h, reduction G J' (s' h) = s₀' h)
    (hn : ∀ h, affineMap G q (s h) = s' h)
    (h : P) (x : Additive (kernel G J)) :
    kernelMapAdd G J q hJ (reductionLiftAction G J s s₀ hs h x) =
      reductionLiftAction G J' s' s₀' hs' h (kernelMapAdd G J q hJ x) := by
  change kernelMapAdd G J q hJ (kernelConjugationAut G J (s h) x) = _
  rw [kernelMapAdd_conjugation, hn]
  rfl

omit [Fact (SqZero J)] [Fact (SqZero J')] in
/-- Multiplicativity defects commute with actual coefficient change. -/
theorem kernelDefect_naturality
    (s : P → AffinePoints G A) (s' : P → AffinePoints G B)
    (s₀ : P →* AffinePoints G (A ⧸ J)) (s₀' : P →* AffinePoints G (B ⧸ J'))
    (hs : ∀ h, reduction G J (s h) = s₀ h)
    (hs' : ∀ h, reduction G J' (s' h) = s₀' h)
    (hn : ∀ h, affineMap G q (s h) = s' h) (h k : P) :
    kernelMapAdd G J q hJ (kernelDefect G J s s₀ hs h k) =
      kernelDefect G J' s' s₀' hs' h k := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [kernelMapAdd_val, kernelDefect_val, map_mul, map_inv, hn]

omit [Fact (SqZero J)] [Fact (SqZero J')] in
/-- Differences of actual homomorphisms commute with coefficient change. -/
theorem kernelDifference_naturality
    (f f' : P →* AffinePoints G A) (g g' : P →* AffinePoints G B)
    (hf : ∀ h, reduction G J (f h) = reduction G J (f' h))
    (hg : ∀ h, reduction G J' (g h) = reduction G J' (g' h))
    (hn : ∀ h, affineMap G q (f h) = g h)
    (hn' : ∀ h, affineMap G q (f' h) = g' h) (h : P) :
    kernelMapAdd G J q hJ (kernelDifference G J f f' hf h) =
      kernelDifference G J' g g' hg h := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [kernelMapAdd_val, kernelDifference_val, map_mul, map_inv, hn, hn']

end Naturality

end Langlands.GroupScheme.Lie.NonaffineKernel
