import Langlands.Algebra.DivisionValuationResidue
import Mathlib.RingTheory.Etale.Basic

/-! # Integral conjugacy of étale embeddings with the same reduction -/

noncomputable section

namespace Langlands.EtaleOrderConjugation

open TensorProduct

section Diagonal

variable (O C : Type*) [CommRing O] [CommRing C] [Algebra O C] [Algebra.Etale O C]

private theorem exists_diagonalIdempotent :
    ∃ e : C ⊗[O] C, Algebra.TensorProduct.lmul' O e = 1 ∧
      ∀ c : C, (c ⊗ₜ[O] (1 : C)) * e = ((1 : C) ⊗ₜ[O] c) * e := by
  obtain ⟨d, hd, hI⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg O C)).mp
      ((Ideal.cotangent_subsingleton_iff _).mp (inferInstance : Subsingleton Ω[C⁄O]))
  have hdmem : d ∈ KaehlerDifferential.ideal O C := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  have hdmap : Algebra.TensorProduct.lmul' O d = 0 := hdmem
  refine ⟨1 - d, by rw [map_sub, map_one, hdmap, sub_zero], fun c => ?_⟩
  apply sub_eq_zero.mp
  rw [← sub_mul]
  have hc : (c ⊗ₜ[O] (1 : C)) - ((1 : C) ⊗ₜ[O] c) ∈
      KaehlerDifferential.ideal O C := by
    rw [← neg_sub]
    exact (KaehlerDifferential.ideal O C).neg_mem
      (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal O c)
  rw [hI] at hc
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hc
  rw [← ha, mul_assoc, mul_sub, mul_one, hd.eq, sub_self, mul_zero]

private def diagonalIdempotent : C ⊗[O] C := (exists_diagonalIdempotent O C).choose

private theorem diagonalIdempotent_lmul :
    Algebra.TensorProduct.lmul' O (diagonalIdempotent O C) = 1 :=
  (exists_diagonalIdempotent O C).choose_spec.1

private theorem diagonalIdempotent_commutes (c : C) :
    (c ⊗ₜ[O] (1 : C)) * diagonalIdempotent O C =
      ((1 : C) ⊗ₜ[O] c) * diagonalIdempotent O C :=
  (exists_diagonalIdempotent O C).choose_spec.2 c

end Diagonal

section Intertwiner

variable {O C A : Type*} [CommRing O] [CommRing C] [Algebra O C]
  [Ring A] [Algebra O A] [Algebra.Etale O C]

private def productOfImages (f g : C →ₐ[O] A) : C ⊗[O] C →ₗ[O] A :=
  (LinearMap.mul' O A).comp (TensorProduct.map f.toLinearMap g.toLinearMap)

omit [Algebra.Etale O C] in
@[simp]
private theorem productOfImages_tmul (f g : C →ₐ[O] A) (x y : C) :
    productOfImages f g (x ⊗ₜ[O] y) = f x * g y := rfl

/-- Evaluate the étale diagonal idempotent by multiplying the two images of its tensor factors. -/
def intertwiner (f g : C →ₐ[O] A) : A := productOfImages f g (diagonalIdempotent O C)

/-- The constructed element intertwines the two original actions of the étale algebra. -/
theorem mul_intertwiner (f g : C →ₐ[O] A) (c : C) :
    f c * intertwiner f g = intertwiner f g * g c := by
  have hleft (t : C ⊗[O] C) :
      productOfImages f g ((c ⊗ₜ[O] (1 : C)) * t) = f c * productOfImages f g t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        productOfImages_tmul, map_mul, mul_assoc]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  have hright (t : C ⊗[O] C) :
      productOfImages f g (((1 : C) ⊗ₜ[O] c) * t) = productOfImages f g t * g c := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        productOfImages_tmul, mul_comm c y, map_mul, mul_assoc]
    | add x y hx hy => simp only [mul_add, add_mul, map_add, hx, hy]
  exact (hleft _).symm.trans
    ((congrArg (productOfImages f g) (diagonalIdempotent_commutes O C c)).trans (hright _))

/-- If the two maps coincide after a ring homomorphism, their intertwiner maps to one. -/
theorem map_intertwiner {B : Type*} [Ring B] (f g : C →ₐ[O] A) (ρ : A →+* B)
    (hρ : ∀ c, ρ (f c) = ρ (g c)) : ρ (intertwiner f g) = 1 := by
  have h (t : C ⊗[O] C) :
      ρ (productOfImages f g t) = (ρ.comp f.toRingHom) (Algebra.TensorProduct.lmul' O t) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [productOfImages_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      change ρ (f x * g y) = ρ (f (x * y))
      simp only [map_mul, ← hρ y]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [intertwiner, h, diagonalIdempotent_lmul, map_one]

end Intertwiner

variable {O C D Γ₀ : Type*} [CommRing O] [CommRing C] [Algebra O C] [Algebra.Etale O C]
  [DivisionRing D] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation D Γ₀)
  [Algebra O v.integer]

/-- Étale embeddings with equal residue are conjugate by a unit in the original integer subring. -/
theorem exists_integerUnit_conj (f g : C →ₐ[O] v.integer)
    (h : ∀ c, DivisionValuation.reduction v (f c) = DivisionValuation.reduction v (g c)) :
    ∃ u : v.integerˣ, ∀ c, f c = (u⁻¹ : v.integerˣ) * g c * (u : v.integer) := by
  have hred := map_intertwiner f g (DivisionValuation.reduction v) h
  have hu : IsUnit (intertwiner f g) :=
    (DivisionValuation.isUnit_iff_value_eq_one v _).mpr
      ((DivisionValuation.reduction_ne_zero_iff v _).mp (hred ▸ one_ne_zero))
  refine ⟨hu.unit⁻¹, fun c => ?_⟩
  change f c = (hu.unit : v.integer) * g c * ((hu.unit⁻¹ : v.integerˣ) : v.integer)
  calc
    f c = (f c * (hu.unit : v.integer)) * ((hu.unit⁻¹ : v.integerˣ) : v.integer) := by
      simp [mul_assoc]
    _ = _ := by rw [hu.unit_spec, mul_intertwiner]

end Langlands.EtaleOrderConjugation
