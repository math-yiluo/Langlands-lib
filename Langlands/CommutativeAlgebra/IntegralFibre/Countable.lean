import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Finite type algebras are countably generated modules

A finite type `R`-algebra `S` is spanned, as an `R`-module, by a countable set. -/

namespace Langlands.CommutativeAlgebra

/-- A finite type `R`-algebra is spanned as an `R`-module by a countable set: the images of the
monomials under a surjection from a polynomial ring in finitely many variables. -/
theorem exists_countable_span_eq_top {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] : ∃ s : Set S, s.Countable ∧ Submodule.span R s = ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let b := MvPolynomial.basisMonomials (Fin n) R
  refine ⟨f.toLinearMap '' Set.range b, (Set.countable_range _).image _, ?_⟩
  rw [Submodule.span_image, b.span_eq, Submodule.map_top, LinearMap.range_eq_top]
  exact hf

end Langlands.CommutativeAlgebra
