import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # One-sided inverses of polynomial substitutions are two-sided -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

/-- A surjective ring endomorphism of a Noetherian commutative ring is injective. -/
theorem injective_of_surjective_of_isNoetherianRing {R : Type*} [CommRing R]
    [IsNoetherianRing R] (f : R →+* R) (hf : Function.Surjective f) :
    Function.Injective f := by
  let c : ℕ →o Ideal R :=
    ⟨fun m => RingHom.ker (f ^ m), fun a b hab x hx => by
      rw [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
      rw [← Nat.sub_add_cancel hab, Function.iterate_add_apply, hx,
        iterate_map_zero]⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance c
  refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := hf.iterate N x
  have hy : y ∈ c (N + 1) := by
    change y ∈ RingHom.ker (f ^ (N + 1))
    rw [RingHom.mem_ker, RingHom.coe_pow, Function.iterate_succ_apply', hx]
  rw [← hN (N + 1) N.le_succ] at hy
  change y ∈ RingHom.ker (f ^ N) at hy
  rwa [RingHom.mem_ker, RingHom.coe_pow] at hy

/-- If substituting `Φ` into `Q` gives the variables, then so does substituting `Q`
into `Φ`: a surjective endomorphism of the Noetherian ring `k[X]` is injective. -/
theorem aeval_eq_X_of_aeval_eq_X {k : Type u} [Field k] {n : ℕ}
    (Φ Q : Fin n → MvPolynomial (Fin n) k) (h : ∀ j, MvPolynomial.aeval Φ (Q j) = MvPolynomial.X j) :
    ∀ i, MvPolynomial.aeval Q (Φ i) = MvPolynomial.X i := by
  have hcomp : (aeval Φ).comp (aeval Q) = AlgHom.id k (MvPolynomial (Fin n) k) := by
    ext j
    simp [h]
  have hright : ∀ f, aeval Φ (aeval Q f) = f := fun f => by
    simpa using DFunLike.congr_fun hcomp f
  have hinj : Function.Injective (aeval Φ : MvPolynomial (Fin n) k →ₐ[k] _) :=
    injective_of_surjective_of_isNoetherianRing (aeval Φ).toRingHom
      fun f => ⟨aeval Q f, hright f⟩
  intro i
  apply hinj
  rw [hright, aeval_X]

end Langlands.GroupScheme.TorusLinearization
