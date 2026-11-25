/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.LinearAlgebra.KernelBasisOfUnitValue
import WeilConjectures.Algebra.Homology.NatSplitFunctionalsHomotopy

/-!
# Natural-degree unit cancellation as a homotopy equivalence

Source: Stacks Project, Algebra, Tag 00MT, the splitting of the trivial complex.
(blueprint: lem-weil-pbc-nat-unit-entry-homotopy-cancellation)
-/

@[expose] public section
universe u v
open CategoryTheory
namespace ChainComplex

/-- Cancel a unit coefficient in a natural-degree finite free complex.
Source: Stacks Project, Algebra, Tag 00MT, proof and its trivial two-term summand.

Proof: Let `u` be the supplied unit coefficient, set `z=b_(j+1)(p)` and
`w=d(z)`, and define `β=u⁻¹` times coordinate `q` on the target and `α=βd`.
Then `α(z)=β(w)=1` and `β(b_j(q))=u⁻¹` is a unit. The kernel-basis theorem
gives bases of `ker α` and `ker β` indexed by `Fin(n_(j+1)-1)` and
`Fin(n_j-1)`. The complex relation gives `α d_(j+2)=0` and `d_j(w)=0`.
Apply `exists_nat_homotopy_equiv_of_split_functionals` to obtain the
complement, its homotopy equivalence with degreewise injective forward map,
and the identifications of its special terms with these kernels. Transfer
the kernel bases using those identifications; at every other degree transfer
the original basis through the identification with the full submodule.
Define `n'` to subtract one at `j+1` and `j`, and agree with `n` elsewhere.
The indices `p` and `q` imply that both original sizes are positive, so the
two asserted successor equations follow by natural-number arithmetic.
This argument requires no augmentation, boundedness, or nontriviality.
(blueprint: lem-weil-pbc-nat-unit-entry-homotopy-cancellation) -/
theorem exists_nat_homotopy_cancellation_of_isUnit_entry
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (n : ℕ → ℕ) (b : ∀ i : ℕ, Module.Basis (Fin (n i)) R (C.X i))
    (j : ℕ) (p : Fin (n (j + 1))) (q : Fin (n j))
    (hu : IsUnit (LinearMap.toMatrix (b (j + 1)) (b j)
      (C.d (j + 1) j).hom q p)) :
    ∃ (C' : ChainComplex (ModuleCat.{max u v} R) ℕ) (n' : ℕ → ℕ)
      (e : HomotopyEquiv C' C),
      (∀ i : ℕ, Nonempty (Module.Basis (Fin (n' i)) R (C'.X i))) ∧
      (∀ i : ℕ, Function.Injective (e.hom.f i).hom) ∧
      n' (j + 1) + 1 = n (j + 1) ∧ n' j + 1 = n j ∧
      (∀ i : ℕ, i ≠ j + 1 → i ≠ j → n' i = n i) := by
  classical
  obtain ⟨u, hu⟩ := hu
  let β : C.X j →ₗ[R] R := (↑(u⁻¹) : R) • (b j).coord q
  let α : C.X (j + 1) →ₗ[R] R := β.comp (C.d (j + 1) j).hom
  let z : C.X (j + 1) := b (j + 1) p
  let w : C.X j := (C.d (j + 1) j).hom z
  have hw : β w = 1 := by
    change (↑(u⁻¹) : R) * (b j).coord q
      ((C.d (j + 1) j).hom (b (j + 1) p)) = 1
    rw [show (b j).coord q ((C.d (j + 1) j).hom (b (j + 1) p)) =
      LinearMap.toMatrix (b (j + 1)) (b j) (C.d (j + 1) j).hom q p by
        simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]]
    rw [← hu]
    simp
  have hz : α z = 1 := hw
  have hα : IsUnit (α (b (j + 1) p)) := by rw [hz]; exact isUnit_one
  have hβ : IsUnit (β (b j q)) := by simp [β, Module.Basis.coord_apply]
  obtain ⟨bi⟩ := (b (j + 1)).exists_basis_ker_of_isUnit_value α p hα
  obtain ⟨bj⟩ := (b j).exists_basis_ker_of_isUnit_value β q hβ
  have hin : ∀ x, α ((C.d (j + 2) (j + 1)).hom x) = 0 := by
    intro x
    have hzero : (C.d (j + 1) j).hom ((C.d (j + 2) (j + 1)).hom x) = 0 := by
      exact congrArg (fun f ↦ f.hom x) (C.d_comp_d (j + 2) (j + 1) j)
    change β ((C.d (j + 1) j).hom ((C.d (j + 2) (j + 1)).hom x)) = 0
    rw [hzero, map_zero]
  have hout : (C.d j (j - 1)).hom w = 0 := by
    exact congrArg (fun f ↦ f.hom z) (C.d_comp_d (j + 1) j (j - 1))
  obtain ⟨C', g, e, hinj⟩ := exists_nat_homotopy_equiv_of_split_functionals
    C j α β z w hz hw (fun _ ↦ rfl) rfl hin hout
  let S : ∀ i : ℕ, Submodule R (C.X i) := fun i ↦
    if h : i = j + 1 then h ▸ LinearMap.ker α
    else if h : i = j then h ▸ LinearMap.ker β else ⊤
  change ∀ i, C'.X i ≃ₗ[R] S i at g
  let n' : ℕ → ℕ := fun i ↦
    if i = j + 1 then n (j + 1) - 1 else if i = j then n j - 1 else n i
  have hne : j ≠ j + 1 := by omega
  refine ⟨C', n', e, ?_, hinj, ?_, ?_, ?_⟩
  · intro i
    by_cases hs : i = j + 1
    · subst i
      have hS : S (j + 1) = LinearMap.ker α := by simp [S]
      let g' := (g (j + 1)).trans (LinearEquiv.ofEq _ _ hS)
      simpa only [n', ite_true] using Nonempty.intro (bi.map g'.symm)
    by_cases ht : i = j
    · subst i
      have hS : S j = LinearMap.ker β := by simp [S]
      let g' := (g j).trans (LinearEquiv.ofEq _ _ hS)
      simpa only [n', ite_eq_right hne, ite_true] using Nonempty.intro (bj.map g'.symm)
    have hS : S i = ⊤ := by simp [S, hs, ht]
    let g' := (g i).trans (LinearEquiv.ofEq _ _ hS)
    let g'' := g'.trans (Submodule.topEquiv : _ ≃ₗ[R] _)
    simpa only [n', ite_eq_right hs, ite_eq_right ht] using Nonempty.intro ((b i).map g''.symm)
  · have hp := p.isLt
    simp only [n', ite_true]
    omega
  · have hq := q.isLt
    simp only [n', ite_eq_right hne, ite_true]
    omega
  · intro i hs ht
    simp [n', hs, ht]

end ChainComplex
