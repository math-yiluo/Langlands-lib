import Langlands.AlgebraicGeometry.NoetherianApproximation.ClosedFiberNormalizationToolsStatement
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.CharP.Quotient
import Mathlib.RingTheory.Ideal.Int

universe u v

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

theorem injective_of_ker_le_span_singleton
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] (f : R →+* S) (r : R)
    (hr : ¬ IsUnit r) (hfr : f r ≠ 0)
    (hker : RingHom.ker f ≤ Ideal.span {r}) : Function.Injective f := by
  have hpow : ∀ n : ℕ, ∀ x : R, f x = 0 → x ∈ (Ideal.span {r}) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp (hker hx)
      have hy : f y = 0 := (mul_eq_zero.mp (by simpa using hx)).resolve_left hfr
      rw [pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton r)) (ih y hy)
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  have h : x ∈ ⨅ n : ℕ, (Ideal.span {r}) ^ n :=
    Ideal.mem_iInf.mpr fun n ↦ hpow n x hx
  simpa [Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {r})
    (by simpa [Ideal.span_singleton_eq_top] using hr)] using h

theorem quasiFiniteAt_of_finite_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] (J : Ideal S)
    [Module.Finite R (S ⧸ J)]
    (hJ : J ≤ (q.under R).map (algebraMap R S)) :
    Algebra.QuasiFiniteAt R q := by
  let f : S ⧸ J →ₐ[R] S ⧸ (q.under R).map (algebraMap R S) :=
    Ideal.quotientMapₐ _ (AlgHom.id R S) hJ
  have : Algebra.QuasiFinite R (S ⧸ (q.under R).map (algebraMap R S)) :=
    .of_surjective_algHom f (Ideal.quotientMap_surjective (H := hJ) Function.surjective_id)
  have : Algebra.WeaklyQuasiFiniteAt R q := inferInstance
  exact .of_weaklyQuasiFiniteAt _

theorem closedFiberNormalizationTools : ClosedFiberNormalizationToolsStatement :=
  ⟨@injective_of_ker_le_span_singleton, @quasiFiniteAt_of_finite_quotient⟩

end Langlands.AlgebraicGeometry.NoetherianApproximation
