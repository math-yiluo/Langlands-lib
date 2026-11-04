import Langlands.LinearAlgebra.PolynomialNonvanishingSpan
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! # Polynomial detection of nonnilpotence in a linear family -/

noncomputable section

universe u v w t s

open Module
open scoped TensorProduct

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {I : Type t} [Fintype I] [DecidableEq I]

/-- Extend the parameters and the endomorphisms of a linear family together. -/
def endomorphismFamilyBaseChange (φ : V →ₗ[k] Module.End k W)
    (K : Type s) [CommRing K] [Algebra k K] :
    K ⊗[k] V →ₗ[K] Module.End K (K ⊗[k] W) :=
  (LinearMap.tensorProduct k K W W).comp (φ.baseChange K)

/-- A nonnilpotent member after scalar extension forces a nonzero coefficient
below the leading coefficient of the ground-field family characteristic polynomial. -/
theorem exists_polyCharpoly_coeff_ne_zero_of_baseChange
    (φ : V →ₗ[k] Module.End k W) (b : Basis I k V)
    {K : Type s} [Field K] [Algebra k K]
    {z : K ⊗[k] V}
    (hz : ¬ IsNilpotent (endomorphismFamilyBaseChange φ K z)) :
    ∃ i < Module.finrank k W, (LinearMap.polyCharpoly φ b).coeff i ≠ 0 := by
  classical
  by_contra! h
  have hp : LinearMap.polyCharpoly φ b = Polynomial.X ^ Module.finrank k W := by
    rw [← LinearMap.polyCharpoly_natDegree φ b,
      (LinearMap.polyCharpoly_monic φ b).eq_X_pow_iff_natDegree_le_natTrailingDegree]
    apply Polynomial.le_natTrailingDegree (LinearMap.polyCharpoly_ne_zero φ b)
    simpa only [LinearMap.polyCharpoly_natDegree] using h
  apply hz
  rw [LinearMap.isNilpotent_iff_charpoly]
  have he := LinearMap.polyCharpoly_map_eq_charpoly
    (endomorphismFamilyBaseChange φ K) (Algebra.TensorProduct.basis K b) z
  rw [endomorphismFamilyBaseChange, LinearMap.polyCharpoly_baseChange,
    hp, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_X] at he
  simpa only [endomorphismFamilyBaseChange, Module.finrank_baseChange] using he.symm

/-- A nonzero characteristic-polynomial coefficient below the leading term
detects nonnilpotence on its nonvanishing locus. -/
theorem not_isNilpotent_of_polyCharpoly_coeff_eval_ne_zero
    (φ : V →ₗ[k] Module.End k W) (b : Basis I k V)
    {i : ℕ} (hi : i < Module.finrank k W) {x : V}
    (hx : MvPolynomial.eval (b.repr x) ((LinearMap.polyCharpoly φ b).coeff i) ≠ 0) :
    ¬ IsNilpotent (φ x) := by
  intro hnil
  rw [LinearMap.polyCharpoly_coeff_eval, hnil.charpoly_eq_X_pow_finrank,
    Polynomial.coeff_X_pow, ite_eq_right hi.ne] at hx
  exact hx rfl

/-- A geometrically nonnilpotent linear family has a ground-field polynomial
nonvanishing locus consisting of nonnilpotent members. -/
theorem exists_polynomial_nonnilpotent_locus
    (φ : V →ₗ[k] Module.End k W) (b : Basis I k V)
    {K : Type s} [Field K] [Algebra k K]
    (hgeo : ∃ z : K ⊗[k] V, ¬ IsNilpotent (endomorphismFamilyBaseChange φ K z)) :
    ∃ p : MvPolynomial I k, p ≠ 0 ∧
      ∀ x : V, MvPolynomial.eval (b.repr x) p ≠ 0 → ¬ IsNilpotent (φ x) := by
  obtain ⟨z, hz⟩ := hgeo
  obtain ⟨i, hi, hp⟩ := exists_polyCharpoly_coeff_ne_zero_of_baseChange φ b hz
  exact ⟨(LinearMap.polyCharpoly φ b).coeff i, hp,
    fun _ hx => not_isNilpotent_of_polyCharpoly_coeff_eval_ne_zero φ b hi hx⟩

/-- Over an infinite field, a geometrically nonnilpotent family has a
nonnilpotent ground-field member and those members span the parameter space. -/
theorem nonnilpotent_locus_spans_of_baseChange [Infinite k]
    (φ : V →ₗ[k] Module.End k W) (b : Basis I k V)
    {K : Type s} [Field K] [Algebra k K]
    (hgeo : ∃ z : K ⊗[k] V, ¬ IsNilpotent (endomorphismFamilyBaseChange φ K z)) :
    (∃ x : V, ¬ IsNilpotent (φ x)) ∧
      Submodule.span k {x : V | ¬ IsNilpotent (φ x)} = ⊤ := by
  obtain ⟨p, hp, hdet⟩ := exists_polynomial_nonnilpotent_locus φ b hgeo
  constructor
  · obtain ⟨x, hx⟩ := exists_polynomial_nonvanishing b hp
    exact ⟨x, hdet x hx⟩
  · apply submodule_eq_top_of_polynomial_nonvanishing b hp
    intro x hx
    exact Submodule.subset_span (hdet x hx)

end Langlands.LinearAlgebra
