import Langlands.BaseChange.CyclicAlgebraStructure
import Langlands.BaseChange.RankOneSigmaLiftNorm
import Langlands.Global.AdelicFunctoriality.NormReduction

/-! # Determinants of matrix norms over cyclic algebras -/

namespace Langlands.BaseChange

open GeneralLinear

universe u v

noncomputable section

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

private theorem prod_range_blocks {M : Type*} [CommMonoid M] (f : ℕ → M) (r d : ℕ) :
    (∏ i ∈ Finset.range (r * d), f i) =
      ∏ j ∈ Finset.range d, ∏ i : Fin r, f (r * j + i.val) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, Finset.prod_range_succ, ih,
      Fin.prod_univ_eq_prod_range (fun i => f (r * d + i)) r]

/-- The scalar determinant norm of a cyclic algebra is the product of the powers of its
chosen automorphism, viewed in the algebra. This includes split and partially split algebras. -/
theorem IsCyclicAlgebra.prod_powers_eq_algebraMap_norm (h : IsCyclicAlgebra σ l) (x : E) :
    (∏ i ∈ Finset.range l, (σ ^ i) x) = algebraMap F E (Algebra.norm F x) := by
  let : Module.Finite F E := h.1
  let f : ℕ → E := fun i => (σ ^ i) x
  have hfix : σ (∏ i ∈ Finset.range l, f i) = ∏ i ∈ Finset.range l, f i := by
    calc
      _ = ∏ i ∈ Finset.range l, f (i + 1) := by
        rw [map_prod]
        exact Finset.prod_congr rfl fun i _ => by
          simp only [f, pow_succ', AlgEquiv.mul_apply]
      _ = _ := by
        obtain ⟨k, hk : l = k + 1⟩ := Nat.exists_eq_succ_of_ne_zero h.pos.ne'
        have hend : f (k + 1) = f 0 := by
          change (σ ^ (k + 1)) x = (σ ^ 0) x
          rw [← hk, h.pow_eq_one, pow_zero]
        rw [hk, Finset.prod_range_succ' f, Finset.prod_range_succ (fun i => f (i + 1)), hend]
  obtain ⟨a, ha⟩ := h.2.2.2.2 _ hfix
  obtain ⟨c⟩ := CyclicAlgebraStructure.exists_coordinates h
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let L := E ⧸ c.m.asIdeal
  let : Field (E ⧸ c.m.asIdeal) := Ideal.Quotient.field c.m.asIdeal
  let q : E →ₐ[F] L := Ideal.Quotient.mkₐ F c.m.asIdeal
  let : Module.Finite F L := c.cyclic.1
  have hwrap₁ (y : E) : q ((σ ^ c.r) y) = c.τ (q y) := c.wrap y
  have hwrap (j : ℕ) (y : E) : q (((σ ^ c.r) ^ j) y) = (c.τ ^ j) (q y) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hwrap₁, ih]
  have hcoord (j : ℕ) (i : Fin c.r) : q (f (c.r * j + i.val)) = (c.τ ^ j) (c.coords x i) := by
    change q ((σ ^ (c.r * j + i.val)) x) = _
    rw [pow_add, pow_mul, AlgEquiv.mul_apply, hwrap, c.coords_apply]
    rfl
  have hquot : q (∏ i ∈ Finset.range l, f i) = algebraMap F L (Algebra.norm F x) := by
    rw [congrArg (fun k => q (∏ i ∈ Finset.range k, f i)) c.degree_eq, prod_range_blocks]
    simp only [map_prod, hcoord]
    rw [Finset.prod_comm, ← Algebra.norm_eq_of_algEquiv c.coords x,
      Langlands.Global.AdelicFunctoriality.norm_pi, map_prod]
    exact Finset.prod_congr rfl fun i _ => (c.cyclic.norm_eq_prod_powers (c.coords x i)).symm
  have ha' : a = Algebra.norm F x :=
    (algebraMap F L).injective ((q.commutes a).symm.trans ((congrArg q ha).trans hquot))
  exact ha.symm.trans (congrArg (algebraMap F E) ha')

/-- The determinant of the ordered matrix norm is the embedded scalar algebra norm
of the determinant, without a field hypothesis on the upper algebra. -/
theorem IsCyclicAlgebra.determinant_cyclicNorm_eq_algebraMap_norm (h : IsCyclicAlgebra σ l)
    (δ : GeneralLinear n E) :
    (determinant (cyclicNorm σ l δ) : E) =
      algebraMap F E (Algebra.norm F (determinant δ : E)) := by
  rw [← h.prod_powers_eq_algebraMap_norm]
  clear h
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cyclicNorm_succ, map_mul, Units.val_mul, ih, Finset.prod_range_succ]
    congr 1
    change (Matrix.map (δ : Matrix (Fin n) (Fin n) E) ((σ ^ l).toRingHom)).det = _
    exact ((σ ^ l).map_det (δ : Matrix (Fin n) (Fin n) E)).symm

/-- Taking determinants of an associated pair gives equality of units over the base field. -/
theorem IsNormAssociated.norm_determinant_units_eq
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (hδγ : IsNormAssociated σ l δ γ)
    (h : IsCyclicAlgebra σ l) :
    Units.map (Algebra.norm F : E →* F) (determinant δ) = determinant γ := by
  let : Module.Finite F E := h.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (h.2.1.symm ▸ h.pos)
  obtain ⟨g, hg⟩ := hδγ
  apply Units.ext
  change Algebra.norm F (determinant δ : E) = (determinant γ : F)
  apply (algebraMap F E).injective
  rw [← h.determinant_cyclicNorm_eq_algebraMap_norm δ]
  have hd := congrArg determinant hg
  rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at hd
  have hd' := congrArg (fun z : Eˣ => (z : E)) hd
  change (determinant (cyclicNorm σ l δ) : E) =
    (Matrix.map (γ : Matrix (Fin n) (Fin n) F) (algebraMap F E)).det at hd'
  exact hd'.trans ((algebraMap F E).map_det (γ : Matrix (Fin n) (Fin n) F)).symm

end

end Langlands.BaseChange
