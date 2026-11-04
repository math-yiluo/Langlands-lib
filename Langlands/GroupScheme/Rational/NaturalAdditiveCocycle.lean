import Langlands.GroupScheme.Unipotent.OneDimensional.Cocycle

/-! # Integrating natural additive two-cocycles in characteristic zero -/

noncomputable section

universe u

open Polynomial

namespace Langlands.GroupScheme.NaturalAdditiveCocycle

open Unipotent.OneDimensional

variable {k : Type u} [Field k]

/-- A scalar two-variable family on coefficient algebras. -/
abbrev ScalarFamily :=
  ∀ (A : Type u) [CommRing A] [Algebra k A], A → A → A

/-- Naturality of a scalar family under every coefficient algebra map. -/
def IsNatural (c : ScalarFamily (k := k)) : Prop :=
  ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x y : A), c B (f x) (f y) = f (c A x y)

/-- The additive two-cocycle identity, without a normalization assumption. -/
def IsCocycle (c : ScalarFamily (k := k)) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (x y z : A),
    c A (x + y) z + c A x y = c A x (y + z) + c A y z

/-- Evaluate the family at the universal pair of polynomial variables. -/
def polynomial (c : ScalarFamily (k := k)) : k[X][X] :=
  c k[X][X] (C X) X

variable {c : ScalarFamily (k := k)}

/-- Naturality identifies the family with evaluation of its universal polynomial. -/
theorem polynomial_ev2 (hn : IsNatural c)
    {A : Type u} [CommRing A] [Algebra k A] (x y : A) :
    ev2 x y (polynomial c) = c A x y := by
  have h := hn k[X][X] A (ev2 x y) (C X) X
  simpa only [polynomial, ev2_C_X, ev2_X] using h.symm

/-- The universal polynomial obeys the polynomial cocycle identity. -/
theorem polynomial_isCocycle (hn : IsNatural c) (hc : IsCocycle c) :
    Unipotent.OneDimensional.IsCocycle (polynomial c) := by
  unfold Unipotent.OneDimensional.IsCocycle defect
  rw [polynomial_ev2 hn, polynomial_ev2 hn, polynomial_ev2 hn, polynomial_ev2 hn]
  have h := hc k[X][X][X] varU varV varW
  rw [h]
  ring

/-- A nonnormalized additive cocycle is constant when its second input is zero. -/
theorem zero_right (hc : IsCocycle c)
    {A : Type u} [CommRing A] [Algebra k A] (x : A) :
    c A x 0 = c A 0 0 := by
  have h := hc A x 0 0
  simp only [add_zero] at h
  exact add_left_cancel h

/-- The zero coefficient in the second variable is the constant at the origin. -/
theorem polynomial_coeff_zero (hn : IsNatural c) (hc : IsCocycle c) :
    (polynomial c).coeff 0 = C (c k 0 0) := by
  have hp := polynomial_ev2 hn (X : k[X]) 0
  have hz := zero_right hc (X : k[X])
  have hconst := hn k k[X] (Algebra.ofId k k[X]) 0 0
  simp only [map_zero] at hconst
  rw [hz, hconst] at hp
  simpa [ev2_apply, eval₂_at_zero, aeval_X_left_apply] using hp

/-- Every natural scalar additive two-cocycle in characteristic zero is a
polynomial coboundary, including a nonzero value at the origin. -/
theorem exists_coboundaryPolynomial [CharZero k]
    (hn : IsNatural c) (hc : IsCocycle c) :
    ∃ f : k[X], ∀ (A : Type u) [CommRing A] [Algebra k A] (x y : A),
      c A x y = aeval (x + y) f - aeval x f - aeval y f := by
  let a := c k 0 0
  let p := polynomial c - C (C a)
  have hconst : C (C a) = coboundary (-C a) := by
    simp only [coboundary, map_neg, aeval_C, algebraMap_apply, algebraMap_eq]
    ring
  have hp : Unipotent.OneDimensional.IsCocycle p := by
    exact (polynomial_isCocycle hn hc).sub (hconst ▸ isCocycle_coboundary (-C a))
  have hp0 : p.coeff 0 = 0 := by
    simp only [p, coeff_sub, polynomial_coeff_zero hn hc, coeff_C_zero, a, sub_self]
  obtain ⟨f, hf⟩ := exists_eq_coboundary_of_charZero hp hp0
  refine ⟨f - C a, ?_⟩
  intro A _ _ x y
  have hpoly : polynomial c = coboundary (f - C a) := by
    have h : coboundary (f - C a) = coboundary f + C (C a) := by
      simp only [coboundary, map_sub, aeval_C, algebraMap_apply, algebraMap_eq]
      ring
    rw [h, ← hf]
    exact (sub_add_cancel _ _).symm
  rw [← polynomial_ev2 hn, hpoly, ev2_coboundary]

/-- A selected polynomial primitive for the natural scalar cocycle. -/
def coboundaryPolynomial [CharZero k] (hn : IsNatural c) (hc : IsCocycle c) : k[X] :=
  Classical.choose (exists_coboundaryPolynomial hn hc)

/-- The selected polynomial integrates the family over every coefficient algebra. -/
theorem coboundaryPolynomial_spec [CharZero k] (hn : IsNatural c) (hc : IsCocycle c)
    {A : Type u} [CommRing A] [Algebra k A] (x y : A) :
    c A x y = aeval (x + y) (coboundaryPolynomial hn hc) -
      aeval x (coboundaryPolynomial hn hc) - aeval y (coboundaryPolynomial hn hc) :=
  Classical.choose_spec (exists_coboundaryPolynomial hn hc) A x y

end Langlands.GroupScheme.NaturalAdditiveCocycle
