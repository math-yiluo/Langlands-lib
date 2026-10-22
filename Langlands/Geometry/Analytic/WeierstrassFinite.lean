import Langlands.Geometry.Analytic.DistinguishedNormalization
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Finite modules obtained from actual distinguished-series division -/

noncomputable section

universe u v

namespace Langlands.Analytic.RestrictedSeries

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
  [Nontrivial A] [NormOneClass A] [NormMulClass A] [CompleteSpace A]
variable {B : Type v} [CommRing B] [_root_.Algebra A B]

/-- If an actual surjective algebra map kills a distinguished series,
polynomials of degree less than its distinguished degree already surject.
The representatives are the remainders constructed by analytic division. -/
theorem degreeLT_surjective_of_distinguished_ker
    (h : Algebra A →ₐ[A] B) (hsurj : Function.Surjective h)
    (f : Algebra A) (d : ℕ) (hf : IsDistinguished f d) (hzero : h f = 0) :
    Function.Surjective
      ((h.toLinearMap.comp (ofPolynomial A).toLinearMap).comp
        (Polynomial.degreeLT A d).subtype) := by
  intro b
  obtain ⟨g, rfl⟩ := hsurj b
  obtain ⟨qr, hqr, _⟩ := existsUnique_distinguished_division f d hf g
  refine ⟨⟨qr.2, Polynomial.mem_degreeLT.mpr hqr.2.1⟩, ?_⟩
  change h (ofPolynomial A qr.2) = h g
  rw [hqr.1, map_add, map_mul, hzero, zero_mul, zero_add]

/-- The finite basis of low-degree polynomials maps to actual module
generators. Neither module finiteness nor a polynomial relation is input. -/
theorem finite_of_surjective_of_distinguished_ker
    (h : Algebra A →ₐ[A] B) (hsurj : Function.Surjective h)
    (f : Algebra A) (d : ℕ) (hf : IsDistinguished f d) (hzero : h f = 0) :
    Module.Finite A B :=
  Module.Finite.of_surjective _ (degreeLT_surjective_of_distinguished_ker
    h hsurj f d hf hzero)

omit [_root_.Algebra A B] in
/-- The same construction for a ring map, with the coefficient action
induced by its genuine restriction to constant series. -/
theorem finite_coefficientMap_of_distinguished_ker
    (h : Algebra A →+* B) (hsurj : Function.Surjective h)
    (f : Algebra A) (d : ℕ) (hf : IsDistinguished f d) (hzero : h f = 0) :
    (h.comp (algebraMap A (Algebra A))).Finite := by
  let := (h.comp (algebraMap A (Algebra A))).toAlgebra
  let hA : Algebra A →ₐ[A] B := { h with commutes' := fun _ => rfl }
  exact finite_of_surjective_of_distinguished_ker hA hsurj f d hf hzero

/-- The actual quotient by any ideal containing a distinguished series
is finite over the coefficient ring. Closedness is unnecessary for this
algebraic consequence of analytic division. -/
theorem finite_quotient_of_distinguished_mem
    (I : Ideal (Algebra A)) (f : Algebra A) (d : ℕ)
    (hf : IsDistinguished f d) (hmem : f ∈ I) :
    Module.Finite A (Algebra A ⧸ I) := by
  apply finite_of_surjective_of_distinguished_ker
    (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ_surjective A I) f d hf
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

omit [_root_.Algebra A B] in
/-- A finite ring map killing a distinguished series remains finite after
restriction to coefficients. This factors through the actual principal-ideal
quotient and composes its proved finite-module structure with the given one. -/
theorem finite_coefficientMap_of_finite_of_distinguished_ker
    (h : Algebra A →+* B) (hfinite : h.Finite)
    (f : Algebra A) (d : ℕ) (hf : IsDistinguished f d) (hzero : h f = 0) :
    (h.comp (algebraMap A (Algebra A))).Finite := by
  let I : Ideal (Algebra A) := Ideal.span {f}
  have hmem : f ∈ I := Ideal.subset_span (Set.mem_singleton f)
  have hle : I ≤ RingHom.ker h := by
    apply Ideal.span_le.mpr
    intro x hx
    have hx' : x = f := Set.mem_singleton_iff.mp hx
    subst x
    exact hzero
  let q := Ideal.Quotient.mk I
  let h' := Ideal.Quotient.lift I h (fun x hx => hle hx)
  have hfactor : h'.comp q = h := by
    ext x
    rfl
  have hfinite' : h'.Finite := RingHom.Finite.of_comp_finite
    (f := q) (by rw [hfactor]; exact hfinite)
  have hqfinite : (q.comp (algebraMap A (Algebra A))).Finite :=
    finite_coefficientMap_of_distinguished_ker q
      (Ideal.Quotient.mk_surjective) f d hf
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hresult := hfinite'.comp hqfinite
  rwa [← RingHom.comp_assoc, hfactor] at hresult

end Langlands.Analytic.RestrictedSeries
