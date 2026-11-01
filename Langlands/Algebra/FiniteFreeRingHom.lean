import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Finite equations for homomorphisms out of an integer-free ring -/

noncomputable section

open Module
open scoped BigOperators

universe uI uO uR uR'

namespace Langlands.FiniteFreeRingHom

variable {I : Type uI} [Fintype I]
variable {O : Type uO} [Ring O]
variable {R : Type uR} [Ring R]
variable {R' : Type uR'} [Ring R']

/-- The unit and basis-multiplication equations in the full target ring. -/
def Relations (b : Basis I ℤ O) (r : I → R) : Prop :=
  (∑ i, b.repr 1 i • r i) = 1 ∧
    ∀ i j, (∑ k, b.repr (b i * b j) k • r k) = r i * r j

/-- Solutions of the finitely many structure-constant equations. -/
abbrev Solutions (b : Basis I ℤ O) (R : Type uR) [Ring R] :=
  {r : I → R // Relations b r}

theorem relations_iff_constr (b : Basis I ℤ O) (r : I → R) :
    Relations b r ↔
      b.constr ℤ r 1 = 1 ∧
        ∀ i j, b.constr ℤ r (b i * b j) = r i * r j := by
  simp only [Relations, Basis.constr_apply_fintype, Basis.equivFun_apply]

omit [Fintype I] in
/-- Multiplication on basis pairs implies multiplication on arbitrary elements. -/
theorem constr_map_mul (b : Basis I ℤ O) (r : I → R)
    (h : ∀ i j, b.constr ℤ r (b i * b j) = r i * r j) :
    ∀ x y, b.constr ℤ r (x * y) = b.constr ℤ r x * b.constr ℤ r y := by
  apply (LinearMap.map_mul_iff (b.constr ℤ r)).2
  apply b.ext
  intro i
  apply b.ext
  intro j
  change b.constr ℤ r (b i * b j) = b.constr ℤ r (b i) * b.constr ℤ r (b j)
  simpa only [Basis.constr_basis] using h i j

/-- Reconstruct an actual unital ring homomorphism from the finite equations. -/
def ofRelations (b : Basis I ℤ O) (r : I → R) (h : Relations b r) : O →+* R where
  __ := (b.constr ℤ r).toAddMonoidHom
  map_one' := ((relations_iff_constr b r).1 h).1
  map_mul' := constr_map_mul b r ((relations_iff_constr b r).1 h).2

@[simp] theorem ofRelations_apply (b : Basis I ℤ O) (r : I → R)
    (h : Relations b r) (x : O) :
    ofRelations b r h x = ∑ i, b.repr x i • r i := by
  exact b.constr_apply_fintype ℤ r x

@[simp] theorem ofRelations_basis (b : Basis I ℤ O) (r : I → R)
    (h : Relations b r) (i : I) :
    ofRelations b r h (b i) = r i :=
  b.constr_basis ℤ r i

omit [Fintype I] in
/-- Every ring homomorphism is the integer-linear reconstruction of its basis values. -/
theorem constr_basis_values (b : Basis I ℤ O) (f : O →+* R) :
    b.constr ℤ (fun i => f (b i)) = f.toIntAlgHom.toLinearMap :=
  b.constr_self ℤ f.toIntAlgHom.toLinearMap

theorem relations_basis_values (b : Basis I ℤ O) (f : O →+* R) :
    Relations b (fun i => f (b i)) := by
  rw [relations_iff_constr, constr_basis_values]
  exact ⟨f.map_one, fun i j => f.map_mul (b i) (b j)⟩

@[simp] theorem ofRelations_basis_values (b : Basis I ℤ O) (f : O →+* R) :
    ofRelations b (fun i => f (b i)) (relations_basis_values b f) = f := by
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (constr_basis_values b f) x

/-- Ring homomorphisms are exactly the tuples satisfying the finite equations. -/
def equiv (b : Basis I ℤ O) : (O →+* R) ≃ Solutions b R where
  toFun f := ⟨fun i => f (b i), relations_basis_values b f⟩
  invFun r := ofRelations b r.val r.property
  left_inv f := ofRelations_basis_values b f
  right_inv r := by
    apply Subtype.ext
    funext i
    exact ofRelations_basis b r.val r.property i

@[simp] theorem equiv_apply (b : Basis I ℤ O) (f : O →+* R) (i : I) :
    (equiv b f).val i = f (b i) := rfl

@[simp] theorem equiv_symm_apply_basis (b : Basis I ℤ O) (r : Solutions b R) (i : I) :
    (equiv b).symm r (b i) = r.val i :=
  ofRelations_basis b r.val r.property i

/-- Postcomposition preserves all the unit and multiplication equations. -/
theorem Relations.map {b : Basis I ℤ O} {r : I → R} (h : Relations b r)
    (g : R →+* R') : Relations b (fun i => g (r i)) := by
  constructor
  · simpa only [map_sum, map_zsmul, map_one] using congrArg g h.1
  · intro i j
    simpa only [map_sum, map_zsmul, map_mul] using congrArg g (h.2 i j)

/-- Componentwise transport of solutions by any unital target ring homomorphism. -/
def map (b : Basis I ℤ O) (g : R →+* R') (r : Solutions b R) : Solutions b R' :=
  ⟨fun i => g (r.val i), r.property.map g⟩

@[simp] theorem map_apply (b : Basis I ℤ O) (g : R →+* R') (r : Solutions b R) (i : I) :
    (map b g r).val i = g (r.val i) := rfl

/-- Reconstruction commutes with arbitrary postcomposition on the target. -/
theorem ofRelations_map (b : Basis I ℤ O) (r : I → R) (h : Relations b r)
    (g : R →+* R') :
    ofRelations b (fun i => g (r i)) (h.map g) = g.comp (ofRelations b r h) := by
  apply RingHom.ext
  intro x
  simp only [ofRelations_apply, RingHom.comp_apply, map_sum, map_zsmul]

theorem equiv_natural (b : Basis I ℤ O) (f : O →+* R) (g : R →+* R') :
    equiv b (g.comp f) = map b g (equiv b f) := by
  apply Subtype.ext
  rfl

theorem equiv_symm_natural (b : Basis I ℤ O) (r : Solutions b R) (g : R →+* R') :
    (equiv b).symm (map b g r) = g.comp ((equiv b).symm r) :=
  ofRelations_map b r.val r.property g

end Langlands.FiniteFreeRingHom
