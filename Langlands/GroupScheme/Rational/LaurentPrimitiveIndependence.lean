import Langlands.GroupScheme.Rational.PrimitivePolynomialRelations
import Langlands.GroupScheme.Rational.LaurentFiniteFrobeniusBasis
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! # Algebraic independence from primitive Laurent Frobenius coordinates -/

noncomputable section

universe u v w

open MvPolynomial

namespace Langlands.GroupScheme.LaurentAugmentation

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {I : Type v}

/-- Additive substitution preserves vanishing at the identity. -/
def additiveAeval {φ : Polynomial k} (hφ : TorusLinearization.IsAddPoly₁ φ)
    (f : space k (I → ℤ)) : space k (I → ℤ) :=
  ⟨Polynomial.aeval f.val φ, by
    rw [mem_space, ← Polynomial.aeval_algHom_apply, (mem_space _).mp f.property]
    simpa only [← Polynomial.coeff_zero_eq_aeval_zero] using hφ.coeff_zero⟩

@[simp] theorem additiveAeval_val {φ : Polynomial k}
    (hφ : TorusLinearization.IsAddPoly₁ φ) (f : space k (I → ℤ)) :
    (additiveAeval hφ f).val = Polynomial.aeval f.val φ := rfl

/-- Finite Laurent encoding commutes with additive one-variable substitutions. -/
theorem finiteEncoding_additiveAeval
    (s : Finset {m : I → ℤ // IsPrimitive p m}) {φ : Polynomial k}
    (hφ : TorusLinearization.IsAddPoly₁ φ) (f : space k (I → ℤ)) :
    finiteEncoding k p I s (additiveAeval hφ f) =
      Polynomial.aeval (finiteEncoding k p I s f) φ := by
  classical
  let term (d : ℕ) : space k (I → ℤ) := ⟨φ.coeff d • f.val ^ d, by
    rw [mem_space, map_smul, map_pow, (mem_space _).mp f.property]
    by_cases hd : d = 0
    · subst d
      simp [hφ.coeff_zero]
    · simp [zero_pow hd]⟩
  have hsum : additiveAeval hφ f = ∑ d ∈ φ.support, term d := by
    apply Subtype.ext
    simp only [additiveAeval_val, Submodule.coe_sum, term]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
    simp only [Algebra.smul_def]
  rw [hsum, map_sum, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨r, hr⟩ : ∃ r, d = p ^ r := by
    by_contra h
    push Not at h
    exact Polynomial.mem_support_iff.mp hd (hφ.coeff_eq_zero k p h)
  have ht : term d = φ.coeff d • frobPower k p I f r := by
    apply Subtype.ext
    simp only [term, Submodule.coe_smul, frobPower, hr]
  rw [ht, map_smul, finiteEncoding_frobPower]
  simp only [hr, Algebra.smul_def]

end Langlands.GroupScheme.LaurentAugmentation

namespace Langlands.GroupScheme.TorusLinearization

variable {k : Type u} [Field k] {n m : ℕ}

open Classical in
/-- Finite-set Frobenius independence detects relations in an injectively indexed family. -/
theorem FrobIndep.indexed {g : Fin n → MvPolynomial (Fin m) k}
    (hind : FrobIndep (Finset.univ.image g)) (hinj : Function.Injective g)
    (ψ : Fin n → Polynomial k) (hψ : ∀ j, IsAddPoly₁ (ψ j))
    (hzero : ∑ j, Polynomial.aeval (g j) (ψ j) = 0) : ∀ j, ψ j = 0 := by
  classical
  let Ψ := Function.extend g ψ (fun _ => 0)
  have hext : ∀ j, Ψ (g j) = ψ j := hinj.extend_apply ψ (fun _ => 0)
  have hΨ : ∀ q ∈ Finset.univ.image g, IsAddPoly₁ (Ψ q) := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    rw [hext]
    exact hψ j
  have hsum : ∑ q ∈ Finset.univ.image g, Polynomial.aeval q (Ψ q) = 0 := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    simpa only [hext] using hzero
  intro j
  rw [← hext]
  exact hind Ψ hΨ hsum (g j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Langlands.GroupScheme.TorusLinearization

namespace Langlands.GroupScheme.PrimitivePolynomial

open LaurentAugmentation TorusLinearization

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {B : Type w} [CommRing B] [Bialgebra k B] {I : Type v} {n : ℕ}

open Classical in
/-- Primitive coordinates with independent finite Laurent encodings are algebraically
independent. The Laurent map only needs to be an algebra map. -/
theorem algebraicIndependent_of_frobIndep_encoding
    (σ : B →ₐ[k] AddMonoidAlgebra k (I → ℤ)) (x : Fin n → B)
    (hx : ∀ j, Bialgebra.IsPrimitiveElem k (x j))
    (q : Fin n → space k (I → ℤ)) (hq : ∀ j, σ (x j) = (q j).val)
    (s : Finset {m : I → ℤ // IsPrimitive p m})
    (hinj : Function.Injective (fun j => finiteEncoding k p I s (q j)))
    (hind : FrobIndep (Finset.univ.image (fun j => finiteEncoding k p I s (q j)))) :
    AlgebraicIndependent k x := by
  rw [algebraicIndependent_iff]
  intro f he
  by_contra hf
  obtain ⟨f, hf, hadd, he⟩ := exists_additive_relation hx ⟨f, hf, he⟩
  let ψ := fun j => part j f
  have hψ : ∀ j, IsAddPoly₁ (ψ j) := fun j => hadd.isAddPoly₁_part j
  have hsum : ∑ j, additiveAeval (hψ j) (q j) = 0 := by
    apply Subtype.ext
    have h := congrArg σ he
    rw [hadd.eq_sum_part] at h
    simp only [map_sum, ← Polynomial.aeval_algHom_apply, aeval_X, hq, map_zero] at h
    simpa only [Submodule.coe_sum, additiveAeval_val, ZeroMemClass.coe_zero] using h
  have hencoded : ∑ j, Polynomial.aeval (finiteEncoding k p I s (q j)) (ψ j) = 0 := by
    have h := congrArg (finiteEncoding k p I s) hsum
    simpa only [map_sum, finiteEncoding_additiveAeval, map_zero] using h
  have hparts := hind.indexed hinj ψ hψ hencoded
  apply hf
  rw [hadd.eq_sum_part]
  simp only [show ∀ j, part j f = 0 from hparts, map_zero, Finset.sum_const_zero]

end Langlands.GroupScheme.PrimitivePolynomial
