import Langlands.Algebra.GenericIrreducibilitySpecialization
import Langlands.Algebra.GenericIrreducibilityHypersurface
import Langlands.Algebra.GenericDensity
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct
open P2MW.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime.P2mGenIrredAff

namespace Langlands.Algebra.GenericIrreducibilitySpreading

theorem tensor_nilradical_isPrime_of_hypersurfaceModel
    {R : Type u} {C : Type v} {K : Type w}
    [CommRing R] [IsDomain R] [CommRing C] [Field K]
    [Algebra R C] [Algebra R K] {d : ℕ}
    (z : Fin d → C) (hz : AlgebraicIndependent R z) (w : C)
    (F : Polynomial (MvPolynomial (Fin d) R)) (hFm : F.Monic)
    (hFroot : F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w = 0)
    (hFirr : Irreducible (F.map (MvPolynomial.map (algebraMap R K))))
    (g : MvPolynomial (Fin d) R) (r : R) (hr : algebraMap R K r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ,
      IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c))
    (q e : ℕ) [ExpChar R q]
    (hrad : ∀ c : C, ∃ m : ℕ,
      ((MvPolynomial.aeval z g) ^ m * c) ^ q ^ e ∈
        Algebra.adjoin R (insert w (Set.range z)))
    (hg : ∀ Q ∈ minimalPrimes (K ⊗[R] C),
      Algebra.TensorProduct.includeRight (A := K) (MvPolynomial.aeval z g) ∉ Q) :
    (nilradical (K ⊗[R] C)).IsPrime := by
  classical
  let A := K ⊗[R] C
  let P := MvPolynomial (Fin d) K
  let t : C →ₐ[R] A := Algebra.TensorProduct.includeRight
  let ψ : P →ₐ[K] A := MvPolynomial.aeval (fun i => t (z i))
  have hψ : Function.Injective ψ :=
    tensor_aeval_injective_of_integral_after_away z hz r hr hint
  have : Nontrivial A := Function.Injective.nontrivial hψ
  let FK : Polynomial P := F.map (MvPolynomial.map (algebraMap R K))
  have hFKm : FK.Monic := hFm.map _
  have hFKprime : Prime FK := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
  have : IsDomain (AdjoinRoot FK) := AdjoinRoot.isDomain_of_prime hFKprime
  have hψmap : ψ.toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      t.toRingHom.comp (MvPolynomial.aeval (R := R) z).toRingHom := by
    apply RingHom.ext
    intro p
    change MvPolynomial.aeval (fun i => t (z i))
      (MvPolynomial.map (algebraMap R K) p) = t (MvPolynomial.aeval z p)
    rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval_apply]
  have hFKroot : FK.eval₂ ψ.toRingHom (t w) = 0 := by
    change (F.map (MvPolynomial.map (algebraMap R K))).eval₂ ψ.toRingHom (t w) = 0
    rw [Polynomial.eval₂_map, hψmap]
    exact (Polynomial.hom_eval₂ F (MvPolynomial.aeval (R := R) z).toRingHom t.toRingHom w).symm.trans
      ((congrArg t hFroot).trans (map_zero t))
  let j : AdjoinRoot FK →ₐ[K] A := AdjoinRoot.liftAlgHom FK ψ (t w) hFKroot
  have hj : Function.Injective j :=
    adjoinRoot_lift_injective_of_monic FK hFKm hFKprime ψ.toRingHom hψ (t w) hFKroot
  let S := Algebra.adjoin R (insert w (Set.range z))
  have htS : ∀ c ∈ S, t c ∈ j.range := by
    intro c hc
    induction hc using Algebra.adjoin_induction with
    | mem c hc =>
      rcases hc with rfl | ⟨i, rfl⟩
      · exact (j.mem_range).mpr ⟨AdjoinRoot.root FK, AdjoinRoot.liftAlgHom_root ..⟩
      · refine (j.mem_range).mpr ⟨AdjoinRoot.of FK (MvPolynomial.X i), ?_⟩
        rw [AdjoinRoot.liftAlgHom_of]
        exact MvPolynomial.aeval_X _ _
    | algebraMap a =>
      rw [t.commutes]
      rw [IsScalarTower.algebraMap_apply R K A]
      exact j.range.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have hgS : MvPolynomial.aeval z g ∈ S := by
    apply Algebra.adjoin_mono (Set.subset_insert _ _)
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (MvPolynomial.aeval z).mem_range_self g
  apply nilradical_isPrime_of_radicial j.toRingHom hj (t (MvPolynomial.aeval z g)) hg
  intro a
  obtain ⟨m, hm⟩ := tensor_uniform_power_containment S j.range
    (MvPolynomial.aeval z g) hgS q e htS hrad a
  exact ⟨m, q ^ e, expChar_pow_pos R q e, (j.mem_range).mp hm⟩

/-- The domain spreading core, with separable closedness of fraction fields. -/
theorem exists_ne_zero_tensor_nilradical_isPrime_of_separablyClosed_range
    {R : Type u} {C : Type v} [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C] [Algebra.FiniteType R C]
    [FaithfulSMul R C]
    (hsc : letI : Algebra (FractionRing R) (FractionRing C) := FractionRing.liftAlgebra R (FractionRing C)
      ∀ θ : FractionRing C, IsSeparable (FractionRing R) θ →
        θ ∈ (algebraMap (FractionRing R) (FractionRing C)).range) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra R K],
      algebraMap R K a ≠ 0 → (nilradical (K ⊗[R] C)).IsPrime := by
  classical
  obtain ⟨r, hr, d, z, w, F, g, hz, hFm, hFroot, hFirr, hg, ⟨q, e, hq, hrad⟩, hint⟩ :=
    exists_hypersurfaceModel_uniform_of_separablyClosed_range hsc
  letI := hq
  let G := (MvPolynomial.optionEquivLeft R (Fin d)).symm F
  have hGirr : Irreducible
      (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) G) := by
    rw [show G = (MvPolynomial.optionEquivLeft R (Fin d)).symm F from rfl,
      map_optionEquivLeft_symm]
    exact (MulEquiv.irreducible_iff
      (MvPolynomial.optionEquivLeft (AlgebraicClosure (FractionRing R)) (Fin d)).symm.toMulEquiv).mpr hFirr
  obtain ⟨b, hb, hBN⟩ :=
    MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure G hGirr
  have hgz : MvPolynomial.aeval z g ≠ 0 := by
    intro h
    apply hg
    apply hz
    simpa only [map_zero] using h
  obtain ⟨c, hc, hmul⟩ :=
    GenericDensity.exists_ne_zero_tensor_mul_injective (R := R) C (MvPolynomial.aeval z g) hgz
  refine ⟨r * b * c, mul_ne_zero (mul_ne_zero hr hb) hc, ?_⟩
  intro K _ _ ha
  rw [map_mul, map_mul] at ha
  have hrK := left_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hbK := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hcK := right_ne_zero_of_mul ha
  have hFK : Irreducible (F.map (MvPolynomial.map (algebraMap R K))) := by
    have hGK := hBN K (algebraMap R K) hbK
    rw [show G = (MvPolynomial.optionEquivLeft R (Fin d)).symm F from rfl,
      map_optionEquivLeft_symm] at hGK
    exact (MulEquiv.irreducible_iff
      (MvPolynomial.optionEquivLeft K (Fin d)).symm.toMulEquiv).mp hGK
  apply tensor_nilradical_isPrime_of_hypersurfaceModel z hz w F hFm hFroot hFK g r hrK hint q e hrad
  intro Q hQ
  have hreg : (1 ⊗ₜ[R] MvPolynomial.aeval z g : K ⊗[R] C) ∈
      nonZeroDivisors (K ⊗[R] C) := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro x hx
    apply hmul K hcK
    simpa only [mul_zero] using hx
  intro hmem
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hQ) hmem hreg

end Langlands.Algebra.GenericIrreducibilitySpreading
