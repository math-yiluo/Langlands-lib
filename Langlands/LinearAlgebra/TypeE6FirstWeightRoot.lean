import Langlands.LinearAlgebra.TypeANegationWeyl

/-! # Three times the first E6 fundamental weight is an integral root sum -/

noncomputable section

namespace Langlands.TypeE6FirstWeightRoot

/-- The simple-root coefficients of three times the first fundamental weight. -/
def coefficients : Fin 6 → ℤ := ![4, 3, 5, 6, 4, 2]

/-- The coefficients pair to three at vertex zero and to zero elsewhere. -/
theorem coefficients_cartan (j : Fin 6) :
    (∑ i : Fin 6, coefficients i * CartanMatrix.E 6 i j) =
      if j = 0 then 3 else 0 := by
  have h : ∀ j : Fin 6,
      (∑ i : Fin 6, coefficients i * CartanMatrix.E 6 i j) =
        if j = 0 then 3 else 0 := by decide
  exact h j

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (e : b.support ≃ Fin 6)
  (hspan : P.corootSpan ℤ = ⊤)
  (hE : ∀ a c : b.support,
    P.pairing a.val c.val = CartanMatrix.E 6 (e a) (e c))

include hE in
/-- The identity takes place in the actual integral weight lattice. -/
theorem three_zsmul_firstWeight :
    (3 : ℤ) • TypeANegationWeyl.firstWeight P b e hspan (by decide) =
      ∑ i : Fin 6, coefficients i • P.root (e.symm i).val := by
  apply IntegralWeylVector.eq_of_pairing_simple_eq P b hspan
  intro a
  simp only [map_zsmul, LinearMap.smul_apply, TypeANegationWeyl.pairing_firstWeight,
    map_sum, LinearMap.sum_apply, P.root_coroot_eq_pairing, hE,
    Equiv.apply_symm_apply, zsmul_eq_mul, Int.cast_id]
  rw [coefficients_cartan]
  simp only [Fin.ext_iff, Fin.val_zero]
  split_ifs <;> norm_num

include hE in
/-- Every additive map annihilating the actual roots kills this triple weight. -/
theorem three_zsmul_image_firstWeight {A : Type*} [AddCommGroup A]
    (f : X →+ A) (hf : ∀ i : J, f (P.root i) = 0) :
    (3 : ℤ) • f (TypeANegationWeyl.firstWeight P b e hspan (by decide)) = 0 := by
  rw [← map_zsmul, three_zsmul_firstWeight P b e hspan hE, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_zsmul, hf, smul_zero]

end Langlands.TypeE6FirstWeightRoot
