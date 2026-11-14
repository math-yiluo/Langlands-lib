import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-! # A unit product from a generating family over a semilocal ring -/

universe u

namespace Langlands.Algebra.Semilocal

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- In a ring with finitely many maximal ideals, every maximal ideal has an element outside it
lying in all the other maximal ideals. -/
theorem exists_separating [Finite (MaximalSpectrum R)] (P : MaximalSpectrum R) :
    ∃ e : R, e ∉ P.asIdeal ∧ ∀ Q : MaximalSpectrum R, Q ≠ P → e ∈ Q.asIdeal := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum R)
  let s : Finset (MaximalSpectrum R) := Finset.univ.erase P
  have hnot : ¬ s.prod (fun Q => Q.asIdeal) ≤ P.asIdeal := by
    rw [P.isMaximal.isPrime.prod_le]
    rintro ⟨Q, hQ, hle⟩
    have hQP : Q = P := MaximalSpectrum.ext (Q.isMaximal.eq_of_le P.isMaximal.ne_top hle)
    exact (Finset.mem_erase.mp hQ).1 hQP
  obtain ⟨e, he, heP⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨e, heP, fun Q hQ => ?_⟩
  have hinf := Ideal.prod_le_inf he
  exact Finset.inf_le (f := fun Q : MaximalSpectrum R => Q.asIdeal)
    (Finset.mem_erase.mpr ⟨hQ, Finset.mem_univ Q⟩) hinf

/-- Let `R` have finitely many maximal ideals and let `M`, `M'` be `R`-submodules of an
`R`-algebra `S` with injective structure map, all of whose products come from `R`. If the
elements of `R` whose images are such products generate the unit ideal, then some single
product is the image of a unit of `R`. -/
theorem exists_isUnit_of_span_eq_top [Finite (MaximalSpectrum R)]
    (hinj : Function.Injective (algebraMap R S)) (M M' : Submodule R S)
    (hprod : ∀ m ∈ M, ∀ m' ∈ M', ∃ r : R, algebraMap R S r = m * m')
    (hspan : Ideal.span {r : R | ∃ m ∈ M, ∃ m' ∈ M', algebraMap R S r = m * m'} = ⊤) :
    ∃ m ∈ M, ∃ m' ∈ M', ∃ r : R, IsUnit r ∧ algebraMap R S r = m * m' := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum R)
  -- a generator outside each maximal ideal
  have hgen : ∀ P : MaximalSpectrum R, ∃ r : R, r ∉ P.asIdeal ∧
      ∃ m ∈ M, ∃ m' ∈ M', algebraMap R S r = m * m' := by
    intro P
    by_contra h
    push Not at h
    have hle : Ideal.span {r : R | ∃ m ∈ M, ∃ m' ∈ M', algebraMap R S r = m * m'} ≤
        P.asIdeal := by
      rw [Ideal.span_le]
      intro r hr
      by_contra hr'
      obtain ⟨m, hm, m', hm', hmm⟩ := hr
      exact h r hr' m hm m' hm' hmm
    rw [hspan] at hle
    exact P.isMaximal.ne_top (top_le_iff.mp hle)
  choose r hrP m hm m' hm' hrm using hgen
  choose e he heQ using exists_separating (R := R)
  choose ρ hρ using fun P Q => hprod (m P) (hm P) (m' Q) (hm' Q)
  refine ⟨∑ P, e P • m P, Submodule.sum_mem _ fun P _ => Submodule.smul_mem _ _ (hm P),
    ∑ Q, e Q • m' Q, Submodule.sum_mem _ fun Q _ => Submodule.smul_mem _ _ (hm' Q),
    ∑ P, ∑ Q, e P * e Q * ρ P Q, ?_, ?_⟩
  · by_contra hu
    obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    let N : MaximalSpectrum R := ⟨I, hI⟩
    have hρNN : ρ N N = r N := hinj (by rw [hρ, hrm])
    have hother : ∀ P Q : MaximalSpectrum R, (P, Q) ≠ (N, N) → e P * e Q * ρ P Q ∈ I := by
      intro P Q hPQ
      by_cases hP : P = N
      · have hQ : N ≠ Q := fun h => hPQ (by rw [hP, h])
        exact I.mul_mem_right _ (I.mul_mem_left _ (heQ Q N hQ))
      · exact I.mul_mem_right _ (I.mul_mem_right _ (heQ P N fun h => hP h.symm))
    have hsplit : ∑ P, ∑ Q, e P * e Q * ρ P Q =
        e N * e N * ρ N N + ∑ x ∈ Finset.univ.erase (N, N), e x.1 * e x.2 * ρ x.1 x.2 := by
      rw [← Fintype.sum_prod_type' (f := fun P Q => e P * e Q * ρ P Q)]
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ (N, N))).symm
    have hrest : ∑ x ∈ Finset.univ.erase (N, N), e x.1 * e x.2 * ρ x.1 x.2 ∈ I :=
      Submodule.sum_mem _ fun x hx => hother x.1 x.2 (Finset.mem_erase.mp hx).1
    have hNN : e N * e N * ρ N N ∈ I := by
      have := I.sub_mem hmem hrest
      rwa [hsplit, add_sub_cancel_right] at this
    rw [hρNN] at hNN
    rcases hI.isPrime.mem_or_mem hNN with h | h
    · rcases hI.isPrime.mem_or_mem h with h | h
      · exact he N h
      · exact he N h
    · exact hrP N h
  · rw [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [map_mul, map_mul, hρ, Algebra.smul_def, Algebra.smul_def]
    ring

end Langlands.Algebra.Semilocal
