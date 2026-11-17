import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Polynomial certificates for the unit ideal in a subring -/

noncomputable section

namespace Langlands.CommutativeAlgebra.InvariantPolynomialCertificate

open MvPolynomial

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {ι ν : Type*} [Fintype ι]

/-- Substitute a linear combination of finite coefficient families, with independent
variables recording the families. -/
def linearFamilyPolynomial (f : ι → ν → A) (F : MvPolynomial ν k) :
    MvPolynomial ι A :=
  aeval (fun j => ∑ i, X i * C (f i j)) F

/-- Evaluating the family variables gives the corresponding linear combination. -/
theorem eval_linearFamilyPolynomial (f : ι → ν → A) (F : MvPolynomial ν k)
    (s : ι → A) :
    eval s (linearFamilyPolynomial f F) =
      aeval (fun j => ∑ i, s i * f i j) F := by
  unfold linearFamilyPolynomial
  change ((aeval s : MvPolynomial ι A →ₐ[A] A).restrictScalars k)
    (aeval (fun j => ∑ i, X i * C (f i j)) F) = _
  rw [comp_aeval_apply]
  simp only [map_sum, map_mul, AlgHom.restrictScalars_apply, aeval_X, aeval_C, Algebra.algebraMap_self_apply]

/-- Scalar-compatible coefficient maps commute with the polynomial construction. -/
theorem map_linearFamilyPolynomial (φ : A →ₐ[k] B)
    (f : ι → ν → A) (F : MvPolynomial ν k) :
    map φ.toRingHom (linearFamilyPolynomial f F) =
      linearFamilyPolynomial (fun i j => φ (f i j)) F := by
  unfold linearFamilyPolynomial
  change ((mapAlgHom φ).restrictScalars k)
    (aeval (fun j => ∑ i, X i * C (f i j)) F) = _
  rw [comp_aeval_apply]
  simp only [map_sum, map_mul, AlgHom.restrictScalars_apply, mapAlgHom_apply, map_X, map_C]
  rfl

/-- The constant coefficient is obtained by evaluating the original polynomial at zero. -/
theorem constantCoeff_linearFamilyPolynomial
    (f : ι → ν → A) (F : MvPolynomial ν k) :
    constantCoeff (linearFamilyPolynomial f F) =
      algebraMap k A (constantCoeff F) := by
  rw [← eval_zero (σ := ι)]
  rw [eval_linearFamilyPolynomial]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, aeval_zero']

omit [Fintype ι] in
/-- A polynomial with coefficients in a subring lifts to a polynomial over that subring. -/
theorem exists_map_subring (S : Subring A) (P : MvPolynomial ι A)
    (hP : ∀ d, P.coeff d ∈ S) :
    ∃ Q : MvPolynomial ι S, map S.subtype Q = P := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro a ha
  obtain ⟨d, _, rfl⟩ := mem_coeffs_iff.mp ha
  exact ⟨⟨P.coeff d, hP d⟩, rfl⟩

omit [Fintype ι] in
/-- A zero constant coefficient and evaluation one give a unit-ideal certificate
over the coefficient subring itself. -/
theorem span_eq_top_of_polynomial_certificate
    (S : Subring A) (s : ι → S) (P : MvPolynomial ι A)
    (hcoeff : ∀ d, P.coeff d ∈ S)
    (hzero : constantCoeff P = 0)
    (hone : eval (fun i => (s i : A)) P = 1) :
    Ideal.span (Set.range s) = ⊤ := by
  obtain ⟨Q, hQ⟩ := exists_map_subring S P hcoeff
  have hQzero : constantCoeff Q = 0 := by
    apply S.subtype_injective
    simpa only [← hQ, constantCoeff_map, map_zero] using hzero
  have hQone : eval s Q = 1 := by
    apply S.subtype_injective
    change S.subtype (eval₂ (RingHom.id S) s Q) = _
    rw [eval₂_comp_left]
    simpa only [← hQ, eval_map, RingHom.comp_id, map_one, Function.comp_def, Subring.subtype_apply] using hone
  let I := Ideal.span (Set.range s)
  apply (Ideal.eq_top_iff_one _).mpr
  have hz : (Ideal.Quotient.mk I) (eval s Q) = 0 := by
    change (Ideal.Quotient.mk I) (eval₂ (RingHom.id S) s Q) = 0
    rw [eval₂_comp_left]
    have hs : (Ideal.Quotient.mk I) ∘ s = 0 := by
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_range_self i))
    rw [hs, eval₂_zero_apply, hQzero, map_zero]
  exact hQone ▸ Ideal.Quotient.eq_zero_iff_mem.mp hz

end Langlands.CommutativeAlgebra.InvariantPolynomialCertificate
