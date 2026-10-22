import Langlands.Cohomology.Weights.Polynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Weight factors over a number field

Actual factor selection over the original coefficient field. The construction
uses normalized irreducible factors; its descent comparison uses rational
minimal polynomials, not continuity of arbitrary complex automorphisms.
-/

noncomputable section

open Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace Langlands.Cohomology.Weights

theorem IsWeilNumber.of_minpoly_root {q : ℕ} {w : ℤ} {z z' : ℂ}
    (hz : IsWeilNumber q w z) (hz' : aeval z' (minpoly ℚ z) = 0) :
    IsWeilNumber q w z' := by
  have hi := hz.1.isIntegral
  have heq : minpoly ℚ z = minpoly ℚ z' :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hi) hz' (minpoly.monic hi)
  refine ⟨(show IsIntegral ℚ z' from ⟨minpoly ℚ z, minpoly.monic hi, hz'⟩).isAlgebraic, ?_⟩
  simpa only [heq] using hz.2

/-- One Weil root of a monic irreducible polynomial forces all its roots, at
every coefficient embedding, to have the same rational-conjugate weight. -/
theorem isPurePolynomial_of_irreducible_root {L : Type*} [Field L] [NumberField L]
    {q : ℕ} {w : ℤ} {P : L[X]} (hP : P.Monic) (hirr : Irreducible P)
    (ι : L →+* ℂ) {z : ℂ} (hz : z ∈ (P.map ι).roots)
    (hweight : IsWeilNumber q w z) : IsPurePolynomial q w P := by
  let : Algebra L ℂ := ι.toAlgebra
  have hzero : aeval z P = 0 := by
    simpa only [aeval_def, ← eval_map, RingHom.algebraMap_toAlgebra, IsRoot.def]
      using (mem_roots (hP.map ι).ne_zero).mp hz
  have hmin : P = minpoly L z :=
    minpoly.eq_of_irreducible_of_monic hirr hzero hP
  have hdvd : P ∣ (minpoly ℚ z).map (algebraMap ℚ L) := by
    rw [hmin]
    exact minpoly.dvd_map_of_isScalarTower ℚ L z
  refine ⟨hP, ?_⟩
  intro κ z' hz'
  apply hweight.of_minpoly_root
  have heval : (P.map κ).eval z' = 0 :=
    (mem_roots (hP.map κ).ne_zero).mp hz'
  have hrat := eval_eq_zero_of_dvd_of_eval_eq_zero (map_dvd κ hdvd) heval
  have hcomp : κ.comp (algebraMap ℚ L) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  simpa only [map_map, hcomp, eval_map, ← aeval_def] using hrat

/-- Select precisely the pure normalized irreducible factors, including their
multiplicities. This polynomial is defined over `L`, without a chosen embedding. -/
def algebraicWeightFactor {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) (P : L[X]) : L[X] :=
  ((normalizedFactors P).filter (IsPurePolynomial q w)).prod

theorem monic_of_mem_normalizedFactors {L : Type*} [Field L] {P Q : L[X]}
    (hQ : Q ∈ normalizedFactors P) : Q.Monic := by
  rw [← normalize_normalized_factor Q hQ]
  exact monic_normalize (ne_zero_of_mem_normalizedFactors hQ)

theorem algebraicWeightFactor_monic {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) (P : L[X]) : (algebraicWeightFactor q w P).Monic := by
  simpa only [Multiset.map_id, algebraicWeightFactor] using
    monic_multiset_prod_of_monic
      ((normalizedFactors P).filter (IsPurePolynomial q w)) id
      (fun Q hQ => ((Multiset.mem_filter.mp hQ).2).1)

theorem algebraicWeightFactor_dvd {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) {P : L[X]} (hP : P.Monic) :
    algebraicWeightFactor q w P ∣ P := by
  have hprod : (normalizedFactors P).prod = P := by
    rw [prod_normalizedFactors_eq hP.ne_zero, hP.normalize_eq_self]
  have hdvd : algebraicWeightFactor q w P ∣ (normalizedFactors P).prod :=
    Multiset.prod_dvd_prod_of_le
      (Multiset.filter_le (IsPurePolynomial q w) (normalizedFactors P))
  rwa [hprod] at hdvd

theorem algebraicWeightFactor_mul {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) {P Q : L[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    algebraicWeightFactor q w (P * Q) =
      algebraicWeightFactor q w P * algebraicWeightFactor q w Q := by
  simp only [algebraicWeightFactor, normalizedFactors_mul hP hQ,
    Multiset.filter_add, Multiset.prod_add]

theorem isPurePolynomial_one {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) : IsPurePolynomial q w (1 : L[X]) := by
  simp [IsPurePolynomial]

theorem IsPurePolynomial.mul {L : Type*} [Field L] [NumberField L]
    {q : ℕ} {w : ℤ} {P Q : L[X]}
    (hP : IsPurePolynomial q w P) (hQ : IsPurePolynomial q w Q) :
    IsPurePolynomial q w (P * Q) := by
  refine ⟨hP.1.mul hQ.1, ?_⟩
  intro ι z hz
  rw [Polynomial.map_mul, roots_mul
    (mul_ne_zero (hP.1.map ι).ne_zero (hQ.1.map ι).ne_zero)] at hz
  exact (Multiset.mem_add.mp hz).elim (hP.2 ι z) (hQ.2 ι z)

theorem isPurePolynomial_multiset_prod {L : Type*} [Field L] [NumberField L]
    {q : ℕ} {w : ℤ} (s : Multiset L[X])
    (hs : ∀ P ∈ s, IsPurePolynomial q w P) : IsPurePolynomial q w s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using isPurePolynomial_one (L := L) q w
  | cons P s ih =>
    simpa only [Multiset.prod_cons] using (hs P (Multiset.mem_cons_self P s)).mul
      (ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)))

theorem algebraicWeightFactor_isPure {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) (P : L[X]) :
    IsPurePolynomial q w (algebraicWeightFactor q w P) :=
  isPurePolynomial_multiset_prod _ fun _ hQ => (Multiset.mem_filter.mp hQ).2

private theorem map_filtered_pure_factors {L : Type*} [Field L] [NumberField L]
    {q : ℕ} (hq : 1 < q) (w : ℤ) (ι : L →+* ℂ) (s : Multiset L[X])
    (hs : ∀ P ∈ s, ∃ v : ℤ, IsPurePolynomial q v P) :
    ((s.filter (IsPurePolynomial q w)).prod).map ι =
      complexWeightFactor q w (s.prod.map ι) := by
  induction s using Multiset.induction_on with
  | empty => simp [complexWeightFactor_one]
  | cons P s ih =>
    obtain ⟨v, hv⟩ := hs P (Multiset.mem_cons_self P s)
    have hs' : ∀ Q ∈ s, ∃ v : ℤ, IsPurePolynomial q v Q :=
      fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
    have hmonic : s.prod.Monic := by
      simpa only [Multiset.map_id] using
        monic_multiset_prod_of_monic s id (fun Q hQ => (hs' Q hQ).choose_spec.1)
    rw [Multiset.prod_cons, Polynomial.map_mul,
      complexWeightFactor_mul q w (hv.1.map ι).ne_zero (hmonic.map ι).ne_zero]
    by_cases hw : IsPurePolynomial q w P
    · simp only [Multiset.filter_cons_of_pos s hw, Multiset.prod_cons,
        Polynomial.map_mul, ih hs',
        complexWeightFactor_eq_self (hw.1.map ι) (hw.hasComplexRootsOfWeight ι)]
    · have hne : w ≠ v := by
        rintro rfl
        exact hw hv
      simp only [Multiset.filter_cons_of_neg s hw, ih hs',
        complexWeightFactor_different_weight hq hne (hv.hasComplexRootsOfWeight ι),
        one_mul]

/-- Purity of every root at one embedding makes each normalized irreducible
factor pure at every embedding. The possible weight may depend on the factor. -/
theorem normalizedFactors_have_weights {L : Type*} [Field L] [NumberField L]
    {q : ℕ} {P : L[X]} (hP : P.Monic) (ι : L →+* ℂ)
    (hroots : ∀ z ∈ (P.map ι).roots, ∃ w : ℤ, IsWeilNumber q w z)
    {Q : L[X]} (hQ : Q ∈ normalizedFactors P) :
    ∃ w : ℤ, IsPurePolynomial q w Q := by
  have hQmonic := monic_of_mem_normalizedFactors hQ
  have hQirr := irreducible_of_normalized_factor Q hQ
  have hdeg : 0 < (Q.map ι).degree := by
    simpa using (degree_pos_of_irreducible hQirr)
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hzQ : z ∈ (Q.map ι).roots := (mem_roots (hQmonic.map ι).ne_zero).mpr hz
  have hzP : z ∈ (P.map ι).roots :=
    Multiset.mem_of_le (roots.le_of_dvd (hP.map ι).ne_zero
      (map_dvd ι (dvd_of_mem_normalizedFactors hQ))) hzQ
  obtain ⟨w, hw⟩ := hroots z hzP
  exact ⟨w, isPurePolynomial_of_irreducible_root hQmonic hQirr ι hzQ hw⟩

/-- Descent of the complex weight factor to the original coefficient field.
Only one complex realization is used in the root hypothesis, but each root
must satisfy the weight condition at all its rational conjugates. -/
theorem map_algebraicWeightFactor {L : Type*} [Field L] [NumberField L]
    {q : ℕ} (hq : 1 < q) (w : ℤ) {P : L[X]} (hP : P.Monic)
    (ι κ : L →+* ℂ)
    (hroots : ∀ z ∈ (P.map ι).roots, ∃ v : ℤ, IsWeilNumber q v z) :
    (algebraicWeightFactor q w P).map κ = complexWeightFactor q w (P.map κ) := by
  have hprod : (normalizedFactors P).prod = P := by
    rw [prod_normalizedFactors_eq hP.ne_zero, hP.normalize_eq_self]
  have h := map_filtered_pure_factors hq w κ (normalizedFactors P)
    (fun _ hQ => normalizedFactors_have_weights hP ι hroots hQ)
  simpa only [hprod, algebraicWeightFactor] using h

end Langlands.Cohomology.Weights
