/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Isomorphisms
import WeilConjectures.AlgebraicGeometry.PolynomialIdealCoefficientsMonomialMembership

@[expose] public section

universe u

open MvPolynomial

namespace MvPolynomial

/-- Coefficient quotient map and induced quotient isomorphism for the coordinate ideal.
Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 07DW.
(blueprint: new-polynomial-ideal-coefficients-map)
The coefficient map is formed componentwise into the ideal quotients; finite support
of a polynomial gives its codomain in the direct sum, monomials give surjectivity,
and the preceding coefficient-membership criterion identifies its kernel. The
first isomorphism theorem for modules then supplies the displayed quotient
isomorphism, characterized by the quotient map. -/
theorem ideal_coefficients_monomial_map
    {R : Type u} [CommRing R] (r i : ℕ) (hr : 1 ≤ r) (hir : i ≤ r)
    (g : Fin i → R) :
    ∃ Φ : MvPolynomial (Fin r) R →ₗ[R]
          Π₀ E : Fin r →₀ ℕ, R ⧸ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}),
        (∀ q E, Φ q E = Ideal.Quotient.mk _ (AddMonoidAlgebra.coeff q E)) ∧
        Function.Surjective Φ ∧
        LinearMap.ker Φ = Submodule.restrictScalars R
          (Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j))) ∧
        ∃ e : (MvPolynomial (Fin r) R ⧸
            Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j))) ≃ₗ[R]
            Π₀ E : Fin r →₀ ℕ, R ⧸ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}),
          ∀ q, e (Ideal.Quotient.mk _ q) = Φ q := by
  classical
  let I : (Fin r →₀ ℕ) → Ideal R :=
    fun E => Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0})
  let J : Ideal (MvPolynomial (Fin r) R) :=
    Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j))
  let c : MvPolynomial (Fin r) R ≃ₗ[R] Π₀ _ : Fin r →₀ ℕ, R :=
    (AddMonoidAlgebra.coeffLinearEquiv R).trans (finsuppLequivDFinsupp R)
  let F : (Π₀ _ : Fin r →₀ ℕ, R) →ₗ[R] Π₀ E, R ⧸ I E :=
    DFinsupp.mapRange.linearMap fun E => (I E).mkQ
  let Φ : MvPolynomial (Fin r) R →ₗ[R] Π₀ E, R ⧸ I E := F.comp c.toLinearMap
  have hcoeff (q : MvPolynomial (Fin r) R) (E : Fin r →₀ ℕ) :
      Φ q E = Ideal.Quotient.mk (I E) (AddMonoidAlgebra.coeff q E) := by
    rfl
  have hF : Function.Surjective F := by
    exact (DFinsupp.mapRange_surjective _ (fun E => (I E).mkQ.map_zero)).2
      fun E => (I E).mkQ_surjective
  have hsurj : Function.Surjective Φ := hF.comp c.surjective
  have hker : LinearMap.ker Φ = J.restrictScalars R := by
    ext q
    rw [LinearMap.mem_ker]
    change Φ q = 0 ↔ q ∈ J
    rw [ideal_coefficients_monomial_membership r i hr hir g q]
    constructor
    · intro h E
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hcoeff, h]
      rfl
    · intro h
      ext E
      exact (hcoeff q E).trans (Ideal.Quotient.eq_zero_iff_mem.mpr (h E))
  refine ⟨Φ, hcoeff, hsurj, hker, ?_⟩
  let e := (Submodule.Quotient.restrictScalarsEquiv R J).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj))
  refine ⟨e, ?_⟩
  intro q
  rfl


end MvPolynomial
