import Mathlib

/-! # Polynomial points with simple integer equations -/

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

open Polynomial

/-- Elements that satisfy an integer polynomial with nonvanishing derivative. -/
def simpleIntegerRootSet (K : Type*) [CommRing K] : Set K :=
  {x | ∃ P : Polynomial ℤ, aeval x P = 0 ∧ aeval x P.derivative ≠ 0}

/-- Simple roots of integer polynomials form an infinite set in an algebraically closed field. -/
lemma infinite_simpleIntegerRootSet (K : Type*) [Field K] [IsAlgClosed K] :
    (simpleIntegerRootSet K).Infinite := by
  classical
  intro hfin
  let T := hfin.toFinset
  obtain ⟨n, hn, hnK⟩ : ∃ n : ℕ, T.card < n ∧ (n : K) ≠ 0 := by
    by_cases h : ((T.card + 1 : ℕ) : K) = 0
    · refine ⟨T.card + 1 + 1, by omega, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, h, zero_add] using (one_ne_zero : (1 : K) ≠ 0)
    · exact ⟨T.card + 1, by omega, h⟩
  let f : Polynomial K := X ^ n - 1
  have hsep : f.Separable := separable_X_pow_sub_C 1 hnK one_ne_zero
  have hcard : f.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree]
    exact natDegree_X_pow_sub_C (r := (1 : K))
  have hsub : f.roots.toFinset ⊆ T := by
    intro x hx
    have hx0 : f.eval x = 0 := (mem_roots hsep.ne_zero).mp (Multiset.mem_toFinset.mp hx)
    have hxd : f.derivative.eval x ≠ 0 := by
      simpa only [eval₂_id] using hsep.eval₂_derivative_ne_zero (RingHom.id K) hx0
    apply hfin.mem_toFinset.mpr
    refine ⟨X ^ n - 1, ?_, ?_⟩
    · simpa only [map_sub, map_pow, aeval_X, map_one, f, eval_sub, eval_pow,
        eval_X, eval_one] using hx0
    · simpa [f, derivative_sub, derivative_pow, derivative_X] using hxd
  have := Finset.card_le_card hsub
  omega

/-- Every nonempty polynomial basic open over a given prime contains a point
whose coordinates satisfy simple integer equations. The index type is arbitrary. -/
lemma exists_prime_simpleIntegerRoots
    {A : Type u} [CommRing A] {ι : Type v}
    (Q : PrimeSpectrum (MvPolynomial ι A))
    (h : MvPolynomial ι A) (hh : h ∉ Q.asIdeal) :
    ∃ a : PrimeSpectrum (MvPolynomial ι A),
      h ∉ a.asIdeal ∧
      a.asIdeal.comap MvPolynomial.C = Q.asIdeal.comap MvPolynomial.C ∧
      ∀ i : ι, ∃ P : Polynomial ℤ,
        aeval (MvPolynomial.X i) P ∈ a.asIdeal ∧
        aeval (MvPolynomial.X i) P.derivative ∉ a.asIdeal := by
  classical
  let p : Ideal A := Q.asIdeal.comap MvPolynomial.C
  have : p.IsPrime := Ideal.comap_isPrime _ _
  let L := AlgebraicClosure p.ResidueField
  let := Ring.toIntAlgebra L
  let φ : A →+* L := (algebraMap p.ResidueField L).comp (algebraMap A p.ResidueField)
  have hker : RingHom.ker φ = p := by
    rw [RingHom.ker_comp_of_injective _ (RingHom.injective _),
      Ideal.ker_algebraMap_residueField]
  have hH : MvPolynomial.map φ h ≠ 0 := by
    intro hz
    have hm : h ∈ Ideal.map MvPolynomial.C p := by
      rw [← hker, ← MvPolynomial.ker_map]
      exact hz
    exact hh (Ideal.map_comap_le hm)
  obtain ⟨α, hα, hαh⟩ : ∃ α : ι → L,
      (∀ i, α i ∈ simpleIntegerRootSet L) ∧
      MvPolynomial.eval α (MvPolynomial.map φ h) ≠ 0 := by
    by_contra! hn
    apply hH
    apply MvPolynomial.funext_set (fun _ : ι ↦ simpleIntegerRootSet L)
      (fun _ ↦ infinite_simpleIntegerRootSet L)
    intro α hα
    simpa only [map_zero] using hn α (fun i ↦ hα i (Set.mem_univ i))
  let F : MvPolynomial ι A →+* L := MvPolynomial.eval₂Hom φ α
  let a : PrimeSpectrum (MvPolynomial ι A) := ⟨RingHom.ker F, RingHom.ker_isPrime F⟩
  have hFaeval (i : ι) (P : Polynomial ℤ) :
      F (aeval (MvPolynomial.X i) P) = aeval (α i) P := by
    simpa only [Polynomial.map_id, F, MvPolynomial.eval₂Hom_X'] using
      (Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id ℤ) (ψ := F)
        (by ext z; simp) P (MvPolynomial.X i))
  refine ⟨a, ?_, ?_, ?_⟩
  · change F h ≠ 0
    simpa only [MvPolynomial.eval_map, F, MvPolynomial.coe_eval₂Hom] using hαh
  · change (RingHom.ker F).comap MvPolynomial.C = p
    ext z
    change F (MvPolynomial.C z) = 0 ↔ z ∈ p
    rw [show F (MvPolynomial.C z) = φ z from MvPolynomial.eval₂Hom_C φ α z]
    exact congr(z ∈ $hker)
  · intro i
    obtain ⟨P, hP, hdP⟩ := hα i
    refine ⟨P, ?_, ?_⟩
    · change F (aeval (MvPolynomial.X i) P) = 0
      rw [hFaeval]
      exact hP
    · change F (aeval (MvPolynomial.X i) P.derivative) ≠ 0
      rw [hFaeval]
      exact hdP

/-- A point in a polynomial basic open, over the same base prime, with simple integer
polynomial equations for all coordinates. -/
structure SimpleIntegerRootPrimeData {A : Type u} [CommRing A] {ι : Type v}
    (Q : PrimeSpectrum (MvPolynomial ι A)) (h : MvPolynomial ι A) where
  prime : PrimeSpectrum (MvPolynomial ι A)
  not_mem : h ∉ prime.asIdeal
  comap_eq : prime.asIdeal.comap MvPolynomial.C = Q.asIdeal.comap MvPolynomial.C
  coordinate : ∀ i : ι, ∃ P : Polynomial ℤ,
    aeval (MvPolynomial.X i) P ∈ prime.asIdeal ∧
    aeval (MvPolynomial.X i) P.derivative ∉ prime.asIdeal

/-- Choose a prime in a polynomial basic open with simple integer equations for all
coordinates. -/
def simpleIntegerRootPrime {A : Type u} [CommRing A] {ι : Type v}
    (Q : PrimeSpectrum (MvPolynomial ι A)) (h : MvPolynomial ι A)
    (hh : h ∉ Q.asIdeal) : SimpleIntegerRootPrimeData Q h :=
  Classical.choice (by
    obtain ⟨a, hha, hbase, hcoord⟩ := exists_prime_simpleIntegerRoots Q h hh
    exact ⟨⟨a, hha, hbase, hcoord⟩⟩)

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
