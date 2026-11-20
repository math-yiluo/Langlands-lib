import Langlands.LinearAlgebra.GaloisVectorDescent
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Ring.Aut
import Mathlib.RingTheory.Norm.Basic

/-! # Hilbert 90 for units in finite-dimensional algebras -/

noncomputable section

universe u v

namespace Langlands.Algebra

open Matrix

variable {k L : Type u} [Field k] [Infinite k] [Field L] [Algebra k L]
  {A : Type v} [Ring A] [Algebra L A] [FiniteDimensional L A]

private theorem exists_unit_in_basis_of_infinite_subfield {I : Type v} [Fintype I]
    (b : Module.Basis I L A) :
    ∃ c : I → k, IsUnit (∑ i, algebraMap k L (c i) • b i) := by
  classical
  let M : Matrix I I (MvPolynomial I L) := .of fun i j =>
    ∑ r, MvPolynomial.X r * MvPolynomial.C (b.repr (b r * b j) i)
  let p := M.det
  have heval (a : I → L) :
      MvPolynomial.eval a p = Algebra.norm L (∑ r, a r • b r) := by
    rw [show MvPolynomial.eval a p = (M.map (MvPolynomial.eval a)).det from
      RingHom.map_det (MvPolynomial.eval a) M, Algebra.norm_eq_matrix_det b]
    congr 1
    ext i j
    simp [M, Algebra.leftMulMatrix_eq_repr_mul, Finset.sum_mul, map_sum,
      map_smul, smul_eq_mul]
  have hp : p ≠ 0 := by
    intro hz
    have hh := heval (fun i => b.repr (1 : A) i)
    have h1 : Algebra.norm L (1 : A) = 1 := map_one _
    rw [hz, map_zero, b.sum_repr, h1] at hh
    exact zero_ne_one hh
  have hbox : ∃ a ∈ Set.pi Set.univ (fun _ : I => Set.range (algebraMap k L)),
      MvPolynomial.eval a p ≠ 0 := by
    by_contra! h
    apply hp
    apply MvPolynomial.funext_set _ (fun _ => Set.infinite_range_of_injective (algebraMap k L).injective)
    simpa only [map_zero] using h
  obtain ⟨a, ha, ha'⟩ := hbox
  choose c hc using fun i => ha i (Set.mem_univ i)
  refine ⟨c, (Algebra.lmul_isUnit_iff (R := L)).mp
    ((LinearMap.isUnit_iff_isUnit_det _).mpr ?_)⟩
  change IsUnit (Algebra.norm L (∑ i, (fun j => algebraMap k L (c j)) i • b i))
  rw [show (fun i => algebraMap k L (c i)) = a from funext hc, ← heval]
  exact isUnit_iff_ne_zero.mpr ha'

variable (H : Subgroup (L ≃ₐ[k] L))

variable (A) in
/-- Every crossed cocycle of units for a supplied semilinear action of a
finite automorphism subgroup is a coboundary over an infinite ground field. -/
def SemilinearUnitHilbert90Statement : Prop :=
  ∀ [Finite H] [Infinite k] [FiniteDimensional L A],
  ∀ (α : H →* RingAut A), (∀ (σ : H) (a : L) (v : A),
      α σ (a • v) = σ.val a • α σ v) →
    ∀ (c : H → Aˣ), c 1 = 1 →
      (∀ σ τ, c (σ * τ) = c σ * Units.map (α σ).toMonoidHom (c τ)) →
      ∃ b : Aˣ, ∀ σ, c σ * Units.map (α σ).toMonoidHom b = b

/-- Hilbert 90 for units in a finite-dimensional algebra with a semilinear action. -/
theorem exists_unit_coboundary [Finite H]
    (α : H →* RingAut A) (hα : ∀ (σ : H) (a : L) (v : A),
      α σ (a • v) = σ.val a • α σ v)
    (c : H → Aˣ) (hc₁ : c 1 = 1)
    (hc : ∀ σ τ, c (σ * τ) = c σ * Units.map (α σ).toMonoidHom (c τ)) :
    ∃ b : Aˣ, ∀ σ, c σ * Units.map (α σ).toMonoidHom b = b := by
  classical
  let f : H → A →+ A := fun σ =>
    { toFun := fun v => (c σ : A) * α σ v
      map_zero' := by simp
      map_add' := fun v w => by simp [mul_add] }
  have hf (σ : H) (v : A) : f σ v = (c σ : A) * α σ v := rfl
  have hone (v : A) : f 1 v = v := by simp [hf, hc₁]
  have hmul (σ τ : H) (v : A) : f (σ * τ) v = f σ (f τ v) := by
    simp only [hf, hc, Units.val_mul, Units.coe_map, map_mul, RingAut.mul_apply, mul_assoc]
    rfl
  have hsmul (σ : H) (a : L) (v : A) : f σ (a • v) = σ.val a • f σ v := by
    rw [hf, hf, hα, mul_smul_comm]
  obtain ⟨s, b, hb⟩ := LinearAlgebra.GaloisVectorDescent.exists_fixed_basis H f hone hmul hsmul
  let : Fintype s := Fintype.ofEquiv _ (b.indexEquiv (Module.finBasis L A)).symm
  obtain ⟨d, hd⟩ := exists_unit_in_basis_of_infinite_subfield (k := k) b
  refine ⟨hd.unit, fun σ => Units.ext ?_⟩
  change (c σ : A) * α σ (hd.unit : A) = hd.unit
  rw [← hf, IsUnit.unit_spec, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsmul, hb, AlgEquiv.commutes]

omit [Infinite k] [FiniteDimensional L A] in
/-- The semilinear unit Hilbert 90 statement for a finite subgroup. -/
theorem semilinearUnitHilbert90 : SemilinearUnitHilbert90Statement A H := by
  intro _ _ _
  exact exists_unit_coboundary H

end Langlands.Algebra
