import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-! # The integral projection from a ring pullback -/

open Polynomial

namespace Langlands.Algebra

/-- In a ring pullback, the projection opposite an integral map is integral
when the other map is surjective. -/
theorem isIntegral_pullbackFst_of_surjective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* T) (g : S →+* T) (hf : Function.Surjective f)
    (hg : g.IsIntegral) : (f.pullbackFst g).IsIntegral := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro r
    exact ⟨X, monic_X, Subsingleton.elim _ _⟩
  let : Nontrivial (f.pullback g) := (f.pullbackFst g).domain_nontrivial
  intro r
  obtain ⟨p, hp, hpr⟩ := hg (f r)
  obtain ⟨q, hqp, _, hq⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (RingHom.surjective_pullbackSnd_of_surjective f g hf) p) hp
  have hqr : f ((q * X).eval₂ (f.pullbackFst g) r) = 0 := by
    rw [hom_eval₂, RingHom.pullback_comm_sq, ← eval₂_map, Polynomial.map_mul,
      map_X, hqp, eval₂_mul, hpr, zero_mul]
  let a : f.pullback g :=
    ⟨((q * X).eval₂ (f.pullbackFst g) r, 0), by simpa using hqr⟩
  refine ⟨q * X - C a, ?_, ?_⟩
  · have hqX : (q * X).Monic := hq.mul monic_X
    have hd : (0 : WithBot ℕ) < (q * X).degree := by
      rw [degree_eq_natDegree hqX.ne_zero, natDegree_mul_X hq.ne_zero]
      exact_mod_cast Nat.zero_lt_succ q.natDegree
    simpa only [sub_eq_add_neg] using
      hqX.add_of_left (by simpa only [degree_neg] using (degree_C_le (a := a)).trans_lt hd)
  · rw [eval₂_sub, eval₂_C]
    exact sub_self _

/-- The first projection, bundled with its proved integrality. -/
def integralPullbackProjection
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* T) (g : S →+* T) (hf : Function.Surjective f)
    (hg : g.IsIntegral) : {φ : f.pullback g →+* R // φ.IsIntegral} :=
  ⟨f.pullbackFst g, isIntegral_pullbackFst_of_surjective f g hf hg⟩

end Langlands.Algebra
