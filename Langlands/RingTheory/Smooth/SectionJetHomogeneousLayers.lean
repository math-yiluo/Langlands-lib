import Langlands.RingTheory.Smooth.SectionJetCoordinates
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous polynomial descriptions of actual augmentation layers -/

noncomputable section

universe u v w w'

namespace Algebra.SectionJet.Coordinates

open MvPolynomial
open Langlands.GroupScheme.CoordinateWeights

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ε : A →ₐ[R] R} {σ : Type w}

/-- A homogeneous degree-`d` polynomial belongs to the `d`th power of the variable ideal. -/
theorem homogeneous_mem_idealOfVars_pow {d : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous d) : p ∈ idealOfVars σ R ^ d := by
  rw [mem_pow_idealOfVars_iff]
  intro e he
  exact le_of_eq (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
    (hp (mem_support_iff.mp he)).symm)

/-- Evaluation of a homogeneous polynomial gives an element of the actual augmentation layer. -/
def homogeneousToLayer (z : σ → A) (hz : ∀ s, ε (z s) = 0) (n : ℕ) :
    homogeneousSubmodule σ R (n + 1) →ₗ[R] Layer ε n :=
  (((Ideal.Quotient.mkₐ R (RingHom.ker ε ^ (n + 1 + 1))).toLinearMap.comp
    (aeval z).toLinearMap).comp (homogeneousSubmodule σ R (n + 1)).subtype).codRestrict _
    (fun p => (mk_mem_layer_iff ε n _).mpr
      (idealOfVars_pow_le_comap z hz (n + 1) (homogeneous_mem_idealOfVars_pow p.property)))

@[simp]
theorem homogeneousToLayer_val (z : σ → A) (hz : ∀ s, ε (z s) = 0) (n : ℕ)
    (p : homogeneousSubmodule σ R (n + 1)) :
    (homogeneousToLayer z hz n p).val = Ideal.Quotient.mk _ (aeval z p.val) := rfl

/-- A homogeneous polynomial of degree `d` cannot have all terms of degree at least `d+1`
unless it is zero. -/
theorem homogeneous_eq_zero_of_mem_pow {d : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous d) (h : p ∈ idealOfVars σ R ^ (d + 1)) : p = 0 := by
  rw [mem_pow_idealOfVars_iff'] at h
  ext e
  by_cases he : e.degree = d
  · exact h e (by omega)
  · exact hp.coeff_eq_zero he

/-- Removing the degree-`d` part of an element of the `d`th variable-ideal power raises
its ideal order. -/
theorem sub_homogeneousComponent_mem_pow {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ idealOfVars σ R ^ d) :
    p - homogeneousComponent d p ∈ idealOfVars σ R ^ (d + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hp ⊢
  intro e he
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases hed : e.degree = d
  · simp [hed]
  · simp [hed, hp e (by omega)]

variable (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, AugmentedAlgebra.classMap ε (z s) = b s)

include b hzb in
/-- Formal smoothness makes the actual homogeneous evaluation into a layer injective. -/
theorem homogeneousToLayer_injective [FormallySmooth R A] (n : ℕ) :
    Function.Injective (homogeneousToLayer z hz n) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  apply Subtype.ext
  change p.val = 0
  apply homogeneous_eq_zero_of_mem_pow p.property
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply quotientMap_aeval_injective z b hz hzb (n + 1 + 1)
  have hp' := congrArg Subtype.val hp
  change Ideal.Quotient.mk _ (aeval z p.val) = 0 at hp'
  exact hp'

include b hzb in
/-- Every actual higher augmentation layer is represented by a homogeneous polynomial
in the chosen cotangent lifts. -/
theorem homogeneousToLayer_surjective [FormallySmooth R A] (n : ℕ) :
    Function.Surjective (homogeneousToLayer z hz n) := by
  intro x
  obtain ⟨p, hp⟩ := (jetEquiv z b hz hzb (n + 1)).surjective x.val
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
  have hq : q ∈ idealOfVars σ R ^ (n + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply quotientMap_aeval_injective z b hz hzb (n + 1)
    change Ideal.Quotient.mk _ (aeval z q) = truncEval z hz (n + 1) 0
    rw [map_zero]
    have hx := x.property
    rw [← hp] at hx
    exact hx
  refine ⟨⟨homogeneousComponent (n + 1) q, homogeneousComponent_mem _ _⟩, ?_⟩
  apply Subtype.ext
  rw [homogeneousToLayer_val]
  change Ideal.Quotient.mk _ (aeval z (homogeneousComponent (n + 1) q)) = x.val
  rw [← hp, jetEquiv_mk, Ideal.Quotient.eq]
  rw [← neg_mem_iff, neg_sub, ← map_sub]
  exact idealOfVars_pow_le_comap z hz _ (sub_homogeneousComponent_mem_pow hq)

/-- The actual successive layer is isomorphic to the homogeneous polynomials of the
corresponding degree, via evaluation at the specified cotangent lifts. -/
def homogeneousEquivLayer [FormallySmooth R A] (n : ℕ) :
    homogeneousSubmodule σ R (n + 1) ≃ₗ[R] Layer ε n :=
  LinearEquiv.ofBijective (homogeneousToLayer z hz n)
    ⟨homogeneousToLayer_injective z b hz hzb n, homogeneousToLayer_surjective z b hz hzb n⟩

end Algebra.SectionJet.Coordinates
