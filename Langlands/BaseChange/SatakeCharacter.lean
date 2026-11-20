import Langlands.BaseChange.SatakeCharacterStatement
import Langlands.Representation.Unramified.ConstituentHeckeScalarProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Existence and separation of Satake characters -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified Polynomial

universe u

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

/-- Prescribed values on the positive-index standard elements are realized by a spectrum
when the last value is nonzero. -/
private theorem exists_standardHeckeScalar_succ {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (r : ℕ) (c : Fin (r + 1) → ℂ) (hc : c (Fin.last r) ≠ 0) :
    ∃ s : Eigenvalues (r + 1), ∀ i : Fin (r + 1), standardHeckeScalar F s i.succ = c i := by
  let Q : ℂ := (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ)
  have hQ : Q ≠ 0 := by
    have hpos : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast Nat.zero_lt_of_lt F.canonicalTopologicalData.residueCardinality_gt_one
    change (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  let a (i : Fin (r + 2)) : ℂ := Q ^ (i.val * (r + 1 - i.val)) * (-1) ^ i.val
  have ha (i : Fin (r + 2)) : a i ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hQ) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  let values := Fin.cons (α := fun _ => ℂ) 1 c
  let b (i : Fin (r + 2)) : ℂ := values i / a i
  let P : ℂ[X] := ∑ i : Fin (r + 2), monomial i.val (b i)
  have hcoeff (i : Fin (r + 2)) : P.coeff i.val = b i := by
    simp [P, coeff_monomial, Fin.val_inj]
  have hP0 : P.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, show 0 = (0 : Fin (r + 2)).val from rfl, hcoeff]
    simp [b, values, a]
  have hdegree : P.natDegree = r + 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      simp only [P, finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_monomial, ite_eq_right (by omega)]
    · change P.coeff (Fin.last (r + 1)).val ≠ 0
      rw [hcoeff]
      have hc' : values (Fin.last (r + 1)) ≠ 0 := by
        simpa [values] using hc
      exact div_ne_zero hc' (ha _)
  obtain ⟨s, hs⟩ := Eigenvalues.exists_eulerPolynomial P hP0
  let s' : Eigenvalues (r + 1) := ⟨(s : Multiset ℂˣ), s.prop.trans hdegree⟩
  have hs' : Eigenvalues.eulerPolynomial s' = P := hs
  refine ⟨s', fun i => ?_⟩
  rw [standardHeckeScalar, elementaryCoefficient, ← mul_assoc, hs', hcoeff]
  change a i.succ * (values i.succ / a i.succ) = c i
  rw [mul_div_cancel₀ _ (ha _)]
  simp [values]

/-- Every Satake parameter gives a character, and those characters separate the
actual spherical Hecke algebra. -/
theorem satakeCharacter : SatakeCharacterStatement.{u} := by
  intro p _ F r
  have existsCharacter (s : Eigenvalues (r + 1)) :
      ∃ ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ, IsSatakeCharacter F r s ω := by
    obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective (r + 1) s
    obtain ⟨A, hA⟩ := SphericalExistence.sphericalConstituentExistence p F r z
    obtain ⟨ω, hω, _⟩ := exists_isSatakeCharacter_of_hasSphericalHeckeSpectrum
      (sphericalConstituentHeckeScalar p F r z A hA)
    exact ⟨ω, hω⟩
  refine ⟨existsCharacter, ?_⟩
  intro f hf
  let : CommRing (SphericalHeckeAlgebra F r) :=
    { (inferInstance : Ring (SphericalHeckeAlgebra F r)) with
      mul_comm := sphericalHeckeAlgebra_mul_comm F r }
  let T (i : Fin (r + 1)) := standardHeckeElement F r i.succ
  have hgen : Algebra.adjoin ℂ (Set.range (standardHeckeElement F r)) ≤
      Algebra.adjoin ℂ (Set.range T) := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => Algebra.subset_adjoin ⟨j, rfl⟩) i
    rw [standardHeckeElement_zero]
    exact Subalgebra.one_mem _
  obtain ⟨m, hm⟩ := sphericalHeckeGeneration p F r f
  have hmem := hgen hm
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨P, hP⟩ := hmem
  change MvPolynomial.aeval T P = standardHeckeElement F r (Fin.last (r + 1)) ^ m * f at hP
  have hPzero : P = 0 := by
    apply MvPolynomial.funext_set (fun _ => ({0} : Set ℂ)ᶜ)
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro c hc
    have hlast : c (Fin.last r) ≠ 0 := by
      simpa using hc (Fin.last r) (Set.mem_univ _)
    obtain ⟨s, hs⟩ := exists_standardHeckeScalar_succ F r c hlast
    obtain ⟨ω, hω⟩ := existsCharacter s
    have hvalues : (fun i => ω (T i)) = c := funext fun i => (hω i.succ).trans (hs i)
    rw [map_zero, ← MvPolynomial.aeval_eq_eval, ← hvalues, ← MvPolynomial.comp_aeval_apply,
      hP, map_mul, hf s ω hω, mul_zero]
  apply ((standardHeckeElement_last_isUnit F r).pow m).mul_right_injective
  change standardHeckeElement F r (Fin.last (r + 1)) ^ m * f =
    standardHeckeElement F r (Fin.last (r + 1)) ^ m * 0
  rw [mul_zero, ← hP, hPzero, map_zero]

end Langlands.BaseChange
