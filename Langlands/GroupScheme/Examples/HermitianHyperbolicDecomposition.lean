import Langlands.GroupScheme.Examples.HermitianIsotropicDimension
import Mathlib.LinearAlgebra.Pi

/-! # Several hyperbolic planes from an actual isotropic subspace -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

variable {L : Type u} [Field L] {c : RingInvolution L}
  {V : Type v} [AddCommGroup V] [Module L V]

/-- Actual linear coordinates displaying `r` hyperbolic planes. The middle
pairing is retained as a function, with no anisotropy assumption. -/
structure HyperbolicDecomposition
    (h : V →ₗ[L] V →ₛₗ[c.bar.toRingHom] L) (r : ℕ) where
  middleDimension : ℕ
  middlePairing : (Fin middleDimension → L) → (Fin middleDimension → L) → L
  coordinates : V ≃ₗ[L]
    (Fin r → L) × ((Fin middleDimension → L) × (Fin r → L))
  pairing_eq : ∀ a b,
    h a b =
      (∑ i, (coordinates a).1 i * c.bar ((coordinates b).2.2 i)) +
      middlePairing (coordinates a).2.1 (coordinates b).2.1 +
      ∑ i, (coordinates a).2.2 i * c.bar ((coordinates b).1 i)

namespace HyperbolicDecomposition

variable (h : V →ₗ[L] V →ₛₗ[c.bar.toRingHom] L)

/-- Display zero hyperbolic planes by choosing ordinary finite coordinates
on the entire space. -/
def zero [FiniteDimensional L V] : HyperbolicDecomposition h 0 where
  middleDimension := Module.finrank L V
  middlePairing a b :=
    h ((Module.finBasis L V).equivFun.symm a) ((Module.finBasis L V).equivFun.symm b)
  coordinates :=
    { toFun := fun v => (0, ((Module.finBasis L V).equivFun v, 0))
      invFun := fun v => (Module.finBasis L V).equivFun.symm v.2.1
      left_inv := fun v => (Module.finBasis L V).equivFun.symm_apply_apply v
      right_inv := fun v => by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · apply Prod.ext
          · exact (Module.finBasis L V).equivFun.apply_symm_apply v.2.1
          · exact Subsingleton.elim _ _
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }
  pairing_eq a b := by simp

/-- Move the two new endpoint coordinates to the heads of the two
hyperbolic coordinate families. -/
def consCoordinates (r m : ℕ) :
    (L × (((Fin r → L) × ((Fin m → L) × (Fin r → L))) × L)) ≃ₗ[L]
      (Fin (r + 1) → L) × ((Fin m → L) × (Fin (r + 1) → L)) where
  toFun v := (Fin.cons v.1 v.2.1.1, (v.2.1.2.1, Fin.cons v.2.2 v.2.1.2.2))
  invFun v := (v.1 0, ((Fin.tail v.1, (v.2.1, Fin.tail v.2.2)), v.2.2 0))
  left_inv v := by simp
  right_inv v := by simp
  map_add' a b := by
    apply Prod.ext
    · exact funext (Fin.cases rfl fun i => rfl)
    · apply Prod.ext
      · rfl
      · exact funext (Fin.cases rfl fun i => rfl)
  map_smul' a b := by
    apply Prod.ext
    · exact funext (Fin.cases rfl fun i => rfl)
    · apply Prod.ext
      · rfl
      · exact funext (Fin.cases rfl fun i => rfl)

variable {h}

/-- The number of middle coordinates plus twice the number of hyperbolic
planes is exactly the ambient dimension. -/
theorem finrank_eq [FiniteDimensional L V] {r : ℕ}
    (d : HyperbolicDecomposition h r) :
    Module.finrank L V = d.middleDimension + 2 * r := by
  have hd := d.coordinates.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hd
  omega

end HyperbolicDecomposition

variable {K : Type u} [Field K] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)

namespace HyperbolicDecomposition

variable {h} {x y : V}
  (hxx : h x x = 0) (hxy : h x y = 1) (hyx : h y x = 1) (hyy : h y y = 0)

include hbar in
/-- Add one actual hyperbolic plane to an existing decomposition of its
orthogonal middle. -/
def cons {r : ℕ}
    (d : HyperbolicDecomposition (hyperbolicMiddlePairing h x y) r) :
    HyperbolicDecomposition h (r + 1) where
  middleDimension := d.middleDimension
  middlePairing := d.middlePairing
  coordinates :=
    ((hyperbolicCoordinates hxx hxy hyx hyy).trans
      ((LinearEquiv.refl L L).prodCongr
        (d.coordinates.prodCongr (LinearEquiv.refl L L)))).trans
      (consCoordinates r d.middleDimension)
  pairing_eq a b := by
    have hp := hyperbolicCoordinates_pairing hbar hxx hxy hyx hyy a b
    have hm := d.pairing_eq
      (hyperbolicProjection hxx hxy hyx hyy a)
      (hyperbolicProjection hxx hxy hyx hyy b)
    change h _ _ = _ at hp
    rw [hp]
    change _ =
      (∑ i : Fin (r + 1), (Fin.cons (α := fun _ => L) (h a y) (d.coordinates
        (hyperbolicProjection hxx hxy hyx hyy a)).1) i *
          (fieldInvolution K L).bar ((Fin.cons (α := fun _ => L) (h b x)
            (d.coordinates (hyperbolicProjection hxx hxy hyx hyy b)).2.2) i)) +
      d.middlePairing
        (d.coordinates (hyperbolicProjection hxx hxy hyx hyy a)).2.1
        (d.coordinates (hyperbolicProjection hxx hxy hyx hyy b)).2.1 +
      ∑ i : Fin (r + 1), (Fin.cons (α := fun _ => L) (h a x) (d.coordinates
        (hyperbolicProjection hxx hxy hyx hyy a)).2.2) i *
          (fieldInvolution K L).bar ((Fin.cons (α := fun _ => L) (h b y)
            (d.coordinates (hyperbolicProjection hxx hxy hyx hyy b)).1) i)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    change h a y * (fieldInvolution K L).bar (h b x) +
      hyperbolicMiddlePairing h x y
        (hyperbolicProjection hxx hxy hyx hyy a)
        (hyperbolicProjection hxx hxy hyx hyy b) +
      h a x * (fieldInvolution K L).bar (h b y) = _
    rw [hm]
    ring

end HyperbolicDecomposition

private theorem nonempty_hyperbolicDecomposition_aux (r : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
      (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
      (_hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x),
      h.Nondegenerate → ∀ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) →
      Module.finrank L W = r → Nonempty (HyperbolicDecomposition h r) := by
  induction r with
  | zero =>
      intro V _ _ _ h _ _ _ _ _
      exact ⟨HyperbolicDecomposition.zero h⟩
  | succ r ih =>
      intro V _ _ _ h hbar hn W hW hr
      have hW0 : W ≠ ⊥ := by
        intro hz
        subst W
        simp only [finrank_bot] at hr
        omega
      obtain ⟨x, hxW, hx⟩ := (Submodule.ne_bot_iff W).mp hW0
      have hxx : h x x = 0 := hW ⟨x, hxW⟩ ⟨x, hxW⟩
      obtain ⟨y, hxy, hyx, hyy⟩ := exists_hyperbolic_partner h hbar hn hx hxx
      have hm : Module.finrank L (isotropicMiddle (h := h) (x := x) (y := y) W) = r := by
        have hd := isotropicMiddle_finrank hxx hxy hyx hyy W hW hxW
        omega
      obtain ⟨d⟩ := ih (hyperbolicMiddlePairing h x y)
        (hyperbolicMiddlePairing_bar h hbar x y)
        (hyperbolicMiddlePairing_nondegenerate hbar hxx hxy hyx hyy hn)
        (isotropicMiddle (h := h) (x := x) (y := y) W)
        (isotropicMiddle_totallyIsotropic W hW) hm
      exact ⟨d.cons hbar hxx hxy hyx hyy⟩

include hbar in
/-- Every actual totally isotropic submodule supplies as many hyperbolic
planes as its finite dimension, in every characteristic. -/
theorem nonempty_hyperbolicDecomposition_of_totallyIsotropic
    [FiniteDimensional L V] (hn : h.Nondegenerate) (W : Submodule L V)
    (hW : ∀ a b : W, h (a : V) (b : V) = 0) :
    Nonempty (HyperbolicDecomposition h (Module.finrank L W)) :=
  nonempty_hyperbolicDecomposition_aux (K := K) (Module.finrank L W) h hbar hn W hW rfl

end Langlands.GroupScheme.HermitianRoot
