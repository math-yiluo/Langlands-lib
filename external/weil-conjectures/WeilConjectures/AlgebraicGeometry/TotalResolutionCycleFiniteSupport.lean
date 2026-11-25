/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Finite support in a left half-plane total complex

Source: Stacks Project, Homology, Tag 09IZ, proof, finite-support representation.
(blueprint: aux-total-resolution-cycle-finite-support)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Every total element in a left half-plane bicomplex has a finite column expansion.
Source: Stacks Project, Homology, Tag 09IZ, proof, finite-support representation.
(blueprint: aux-total-resolution-cycle-finite-support)

Proof. Map the dependent finite-support vectors of the modules in bidegrees
(-i,n+i), for natural i, into the total module by summing their inclusions.
This map is epi: equality after it can be tested on singleton vectors, which
covers every nonpositive-column summand; positive-column summands are zero.
The total coproduct's universal property then gives equality on the total module.
An epimorphism of modules is surjective, so choose a finite-support preimage of z.
Bound its support by its finite supremum r (zero for empty support), and extend
its reconstruction sum to the range r+1 by adding zero terms. This uses neither
a cycle condition nor horizontal exactness. -/
theorem total_resolution_element_finite_support
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (z : (K.total (ComplexShape.up ℤ)).X n) :
    ∃ r : ℕ, ∃ x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)),
      z = ∑ i ∈ Finset.range (r + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i) := by
  classical
  let M := fun i : ℕ ↦ ((K.X (-(i : ℤ))).X (n + (i : ℤ)) : Type _)
  let f : (Π₀ i, M i) →ₗ[R] (K.total (ComplexShape.up ℤ)).X n :=
    DFinsupp.lsum ℕ (fun i ↦
      (K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n).hom)
  let F : ModuleCat.of R (Π₀ i, M i) ⟶ (K.total (ComplexShape.up ℤ)).X n :=
    ModuleCat.ofHom f
  have hF : Epi F := by
    constructor
    intro A g h hgh
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hpq' : p + q = n := by simpa using hpq
    by_cases hp : 0 < p
    · have hz : IsZero ((K.X p).X q) :=
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).map_isZero
          (h_positive p hp)
      exact hz.eq_of_src _ _
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, p = -(i : ℤ) := ⟨(-p).toNat, by omega⟩
      have hqi : q = n + (i : ℤ) := by omega
      subst q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      have he := congrArg (fun k ↦ k (DFinsupp.single i a)) hgh
      simpa [F, f, DFinsupp.lsum_single, K.ιTotalOrZero_eq _ _ _ _ hpq] using he
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective F).mp hF z
  refine ⟨x.support.sup id, fun i ↦ x i, ?_⟩
  rw [← hx]
  change f x = _
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  exact DFinsupp.sum_of_support_subset
    (fun i hi ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))
    (fun i _ ↦ map_zero _)

end WeilConjectures.DerivedTotalResolution
