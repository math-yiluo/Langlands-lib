import Langlands.Representation.Unramified.Eigenvalues
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.Cofinite

/-! # Finite-exception systems of nonzero complex spectra

This numerical layer neither constructs automorphic representations nor chooses
their spectra. Applications must supply the connection to actual local objects.
-/

noncomputable section

open scoped BigOperators

universe uI uJ

namespace Langlands.Unramified

namespace Eigenvalues

variable {J : Type uJ} [Fintype J] {n : J → ℕ}

/-- Concatenate a finite family with varying ranks, retaining repetitions. -/
def finiteSum (s : ∀ j, Eigenvalues (n j)) : Eigenvalues (∑ j, n j) :=
  ⟨∑ j, (s j : Multiset ℂˣ), by simp⟩

@[simp] theorem powerTrace_finiteSum (s : ∀ j, Eigenvalues (n j)) (k : ℕ) :
    (finiteSum s).powerTrace k = ∑ j, (s j).powerTrace k := by
  classical
  have h (t : Finset J) :
      ((∑ j ∈ t, (s j : Multiset ℂˣ)).map (fun z : ℂˣ => (z : ℂ) ^ k)).sum =
        ∑ j ∈ t, (s j).powerTrace k := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih => simp [hj, ih, powerTrace]
  exact h Finset.univ

@[simp] theorem eulerPolynomial_finiteSum (s : ∀ j, Eigenvalues (n j)) :
    (finiteSum s).eulerPolynomial = ∏ j, (s j).eulerPolynomial := by
  classical
  have h (t : Finset J) :
      ((∑ j ∈ t, (s j : Multiset ℂˣ)).map
        (fun z : ℂˣ => 1 - Polynomial.C (z : ℂ) * Polynomial.X)).prod =
        ∏ j ∈ t, (s j).eulerPolynomial := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih => simp [hj, ih, eulerPolynomial]
  exact h Finset.univ

end Eigenvalues

/-- Numerical nonzero complex spectra of fixed rank outside a finite set.
There is no local representation or arithmetic realization field. -/
structure SpectralSystem (I : Type uI) (n : ℕ) where
  exceptional : Finset I
  eigenvalues : ∀ v ∉ exceptional, Eigenvalues n

namespace SpectralSystem

variable {I : Type uI} {n m l : ℕ}

def powerTrace (s : SpectralSystem I n) (v : I) (hv : v ∉ s.exceptional)
    (k : ℕ) : ℂ := (s.eigenvalues v hv).powerTrace k

def eulerPolynomial (s : SpectralSystem I n) (v : I)
    (hv : v ∉ s.exceptional) : Polynomial ℂ := (s.eigenvalues v hv).eulerPolynomial

@[simp] theorem powerTrace_zero (s : SpectralSystem I n) (v : I)
    (hv : v ∉ s.exceptional) : s.powerTrace v hv 0 = n :=
  Eigenvalues.powerTrace_zero _

@[simp] theorem eulerPolynomial_eval_zero (s : SpectralSystem I n) (v : I)
    (hv : v ∉ s.exceptional) : (s.eulerPolynomial v hv).eval 0 = 1 :=
  Eigenvalues.eulerPolynomial_eval_zero _

theorem eulerPolynomial_ne_zero (s : SpectralSystem I n) (v : I)
    (hv : v ∉ s.exceptional) : s.eulerPolynomial v hv ≠ 0 :=
  Eigenvalues.eulerPolynomial_ne_zero _

@[simp] theorem eulerPolynomial_natDegree (s : SpectralSystem I n) (v : I)
    (hv : v ∉ s.exceptional) : (s.eulerPolynomial v hv).natDegree = n :=
  Eigenvalues.eulerPolynomial_natDegree _

/-- Forget the data at additional exceptional indices. -/
def restrict (s : SpectralSystem I n) (T : Finset I) (hT : s.exceptional ⊆ T) :
    SpectralSystem I n where
  exceptional := T
  eigenvalues v hv := s.eigenvalues v (fun h => hv (hT h))

@[simp] theorem restrict_powerTrace (s : SpectralSystem I n) (T : Finset I)
    (hT : s.exceptional ⊆ T) (v : I) (hv : v ∉ T) (k : ℕ) :
    (s.restrict T hT).powerTrace v hv k =
      s.powerTrace v (fun h => hv (hT h)) k := rfl

@[simp] theorem restrict_eulerPolynomial (s : SpectralSystem I n) (T : Finset I)
    (hT : s.exceptional ⊆ T) (v : I) (hv : v ∉ T) :
    (s.restrict T hT).eulerPolynomial v hv =
      s.eulerPolynomial v (fun h => hv (hT h)) := rfl

/-- All positive traces agree outside one finite set, uniformly in the power. -/
def SamePowerTraces (s : SpectralSystem I n) (t : SpectralSystem I m) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∀ (hs : v ∉ s.exceptional) (ht : v ∉ t.exceptional),
    ∀ k : ℕ, 0 < k → s.powerTrace v hs k = t.powerTrace v ht k

/-- Euler denominator polynomials agree outside a finite set. -/
def SameEulerPolynomials (s : SpectralSystem I n) (t : SpectralSystem I m) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∀ (hs : v ∉ s.exceptional) (ht : v ∉ t.exceptional),
    s.eulerPolynomial v hs = t.eulerPolynomial v ht

theorem samePowerTraces_refl (s : SpectralSystem I n) : s.SamePowerTraces s :=
  Filter.Eventually.of_forall fun _ _ _ _ _ => rfl

theorem SamePowerTraces.symm {s : SpectralSystem I n} {t : SpectralSystem I m}
    (h : s.SamePowerTraces t) : t.SamePowerTraces s :=
  h.mono fun _ hv ht hs k hk => (hv hs ht k hk).symm

theorem SamePowerTraces.trans {s : SpectralSystem I n} {t : SpectralSystem I m}
    {u : SpectralSystem I l} (hst : s.SamePowerTraces t) (htu : t.SamePowerTraces u) :
    s.SamePowerTraces u := by
  filter_upwards [hst, htu, t.exceptional.eventually_cofinite_notMem] with v hst htu ht
  intro hs hu k hk
  exact (hst hs ht k hk).trans (htu ht hu k hk)

theorem sameEulerPolynomials_refl (s : SpectralSystem I n) : s.SameEulerPolynomials s :=
  Filter.Eventually.of_forall fun _ _ _ => rfl

theorem SameEulerPolynomials.symm {s : SpectralSystem I n} {t : SpectralSystem I m}
    (h : s.SameEulerPolynomials t) : t.SameEulerPolynomials s :=
  h.mono fun _ hv ht hs => (hv hs ht).symm

theorem SameEulerPolynomials.trans {s : SpectralSystem I n} {t : SpectralSystem I m}
    {u : SpectralSystem I l} (hst : s.SameEulerPolynomials t)
    (htu : t.SameEulerPolynomials u) : s.SameEulerPolynomials u := by
  filter_upwards [hst, htu, t.exceptional.eventually_cofinite_notMem] with v hst htu ht
  intro hs hu
  exact (hst hs ht).trans (htu ht hu)

theorem samePowerTraces_restrict (s : SpectralSystem I n) (T : Finset I)
    (hT : s.exceptional ⊆ T) : s.SamePowerTraces (s.restrict T hT) :=
  Filter.Eventually.of_forall fun _ _ _ _ _ => rfl

theorem sameEulerPolynomials_restrict (s : SpectralSystem I n) (T : Finset I)
    (hT : s.exceptional ⊆ T) : s.SameEulerPolynomials (s.restrict T hT) :=
  Filter.Eventually.of_forall fun _ _ _ => rfl

section FiniteFamily

variable {J : Type uJ} [Fintype J] {rank : J → ℕ}

/-- The common exceptional set is the finite union of the individual ones. -/
def familyExceptional (s : ∀ j, SpectralSystem I (rank j)) : Finset I := by
  classical
  exact Finset.univ.biUnion fun j => (s j).exceptional

theorem exceptional_subset_family (s : ∀ j, SpectralSystem I (rank j)) (j : J) :
    (s j).exceptional ⊆ familyExceptional s := by
  classical
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hv⟩

theorem not_mem_exceptional (s : ∀ j, SpectralSystem I (rank j))
    (v : I) (hv : v ∉ familyExceptional s) (j : J) : v ∉ (s j).exceptional :=
  fun h => hv (exceptional_subset_family s j h)

/-- The numerical direct sum of mixed-rank systems outside their common
exceptional set. Repeated summands retain their eigenvalue multiplicities. -/
def finiteSum (s : ∀ j, SpectralSystem I (rank j)) :
    SpectralSystem I (∑ j, rank j) where
  exceptional := familyExceptional s
  eigenvalues v hv :=
    Eigenvalues.finiteSum fun j => (s j).eigenvalues v (not_mem_exceptional s v hv j)

@[simp] theorem finiteSum_powerTrace (s : ∀ j, SpectralSystem I (rank j))
    (v : I) (hv : v ∉ familyExceptional s) (k : ℕ) :
    (finiteSum s).powerTrace v hv k =
      ∑ j, (s j).powerTrace v (not_mem_exceptional s v hv j) k :=
  Eigenvalues.powerTrace_finiteSum _ _

@[simp] theorem finiteSum_eulerPolynomial (s : ∀ j, SpectralSystem I (rank j))
    (v : I) (hv : v ∉ familyExceptional s) :
    (finiteSum s).eulerPolynomial v hv =
      ∏ j, (s j).eulerPolynomial v (not_mem_exceptional s v hv j) :=
  Eigenvalues.eulerPolynomial_finiteSum _

/-- Equality of the combined trace systems is exactly equality of mixed-rank
trace sums outside one finite set, with the same set for every positive power. -/
theorem finiteSum_samePowerTraces_iff {K : Type*} [Fintype K] {rank' : K → ℕ}
    (s : ∀ j, SpectralSystem I (rank j)) (t : ∀ j, SpectralSystem I (rank' j)) :
    (finiteSum s).SamePowerTraces (finiteSum t) ↔
      ∀ᶠ v in Filter.cofinite,
        ∀ (hs : v ∉ familyExceptional s) (ht : v ∉ familyExceptional t),
          ∀ k : ℕ, 0 < k →
            (∑ j, (s j).powerTrace v (not_mem_exceptional s v hs j) k) =
              ∑ j, (t j).powerTrace v (not_mem_exceptional t v ht j) k := by
  constructor
  · intro h
    exact h.mono fun v hv hs ht k hk =>
      (finiteSum_powerTrace s v hs k).symm.trans
        ((hv hs ht k hk).trans (finiteSum_powerTrace t v ht k))
  · intro h
    exact h.mono fun v hv hs ht k hk =>
      (finiteSum_powerTrace s v hs k).trans
        ((hv hs ht k hk).trans (finiteSum_powerTrace t v ht k).symm)

theorem finiteSum_sameEulerPolynomials_iff {K : Type*} [Fintype K] {rank' : K → ℕ}
    (s : ∀ j, SpectralSystem I (rank j)) (t : ∀ j, SpectralSystem I (rank' j)) :
    (finiteSum s).SameEulerPolynomials (finiteSum t) ↔
      ∀ᶠ v in Filter.cofinite,
        ∀ (hs : v ∉ familyExceptional s) (ht : v ∉ familyExceptional t),
          (∏ j, (s j).eulerPolynomial v (not_mem_exceptional s v hs j)) =
            ∏ j, (t j).eulerPolynomial v (not_mem_exceptional t v ht j) := by
  constructor
  · intro h
    exact h.mono fun v hv hs ht =>
      (finiteSum_eulerPolynomial s v hs).symm.trans
        ((hv hs ht).trans (finiteSum_eulerPolynomial t v ht))
  · intro h
    exact h.mono fun v hv hs ht =>
      (finiteSum_eulerPolynomial s v hs).trans
        ((hv hs ht).trans (finiteSum_eulerPolynomial t v ht).symm)

end FiniteFamily

end SpectralSystem
end Langlands.Unramified
