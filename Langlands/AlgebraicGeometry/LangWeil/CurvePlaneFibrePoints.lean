import Langlands.AlgebraicGeometry.LangWeil.CurvePlaneRadicialPoints
import Langlands.Algebra.GenericIrreducibilityAffineModel

/-! # Rational points of a fibre and of its hypersurface model -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

open Langlands.Algebra.GenericIrreducibilitySpreading

/-- A power `q ^ e` of the exponential characteristic of the base is a power of the
exponential characteristic of any field over it. -/
theorem exists_pow_eq_pow_of_expChar
    {A κ : Type*} [CommRing A] [IsDomain A] [Field κ] [Algebra A κ]
    (q e p : ℕ) [ExpChar A q] [ExpChar κ p] : ∃ n : ℕ, q ^ e = p ^ n := by
  cases ‹ExpChar A q› with
  | zero => exact ⟨0, by simp⟩
  | prime hq =>
    have : CharP κ q := CharP.of_ringHom_of_ne_zero (algebraMap A κ) q hq.ne_zero
    have : ExpChar κ q := ExpChar.prime hq
    exact ⟨e, by rw [ExpChar.eq ‹ExpChar κ q› ‹ExpChar κ p›]⟩

/-- The `A`-points of `C` not killing `g(z)` correspond to the points of the specialized
hypersurface model not killing `g`. -/
theorem card_algHom_good_eq
    {A : Type u} {C : Type v} {κ : Type w} [CommRing A] [IsDomain A] [CommRing C]
    [Field κ] [Finite κ] [Algebra A C] [Algebra A κ] {d : ℕ}
    (z : Fin d → C) (hz : AlgebraicIndependent A z) (w : C)
    (F : Polynomial (MvPolynomial (Fin d) A)) (hFm : F.Monic)
    (hFroot : F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) A →ₐ[A] C).toRingHom w = 0)
    (hFirr : Irreducible (F.map (MvPolynomial.map (algebraMap A κ))))
    (g : MvPolynomial (Fin d) A) (r : A) (hr : algebraMap A κ r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ,
      IsIntegral (Algebra.adjoin A (Set.range z)) (r ^ n • c))
    (q e : ℕ) [ExpChar A q]
    (hrad : ∀ c : C, ∃ m : ℕ,
      ((MvPolynomial.aeval z g) ^ m * c) ^ q ^ e ∈
        Algebra.adjoin A (insert w (Set.range z))) :
    Nat.card {ψ : C →ₐ[A] κ // ψ (MvPolynomial.aeval z g) ≠ 0} =
      Nat.card {χ : AdjoinRoot (F.map (MvPolynomial.map (algebraMap A κ))) →ₐ[κ] κ //
        χ (AdjoinRoot.of _ (MvPolynomial.map (algebraMap A κ) g)) ≠ 0} := by
  classical
  let T := κ ⊗[A] C
  let P := MvPolynomial (Fin d) κ
  let t : C →ₐ[A] T := Algebra.TensorProduct.includeRight
  let ψ : P →ₐ[κ] T := MvPolynomial.aeval (fun i => t (z i))
  have hψ : Function.Injective ψ :=
    tensor_aeval_injective_of_integral_after_away z hz r hr hint
  let FK : Polynomial P := F.map (MvPolynomial.map (algebraMap A κ))
  have hFKm : FK.Monic := hFm.map _
  have hFKprime : Prime FK := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
  have hψmap : ψ.toRingHom.comp (MvPolynomial.map (algebraMap A κ)) =
      t.toRingHom.comp (MvPolynomial.aeval (R := A) z).toRingHom := by
    apply RingHom.ext
    intro p
    change MvPolynomial.aeval (fun i => t (z i))
      (MvPolynomial.map (algebraMap A κ) p) = t (MvPolynomial.aeval z p)
    rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval_apply]
  have hFKroot : FK.eval₂ ψ.toRingHom (t w) = 0 := by
    change (F.map (MvPolynomial.map (algebraMap A κ))).eval₂ ψ.toRingHom (t w) = 0
    rw [Polynomial.eval₂_map, hψmap]
    exact (Polynomial.hom_eval₂ F (MvPolynomial.aeval (R := A) z).toRingHom t.toRingHom w).symm.trans
      ((congrArg t hFroot).trans (map_zero t))
  let j : AdjoinRoot FK →ₐ[κ] T := AdjoinRoot.liftAlgHom FK ψ (t w) hFKroot
  have hj : Function.Injective j :=
    adjoinRoot_lift_injective_of_monic FK hFKm hFKprime ψ.toRingHom hψ (t w) hFKroot
  let S := Algebra.adjoin A (insert w (Set.range z))
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
      rw [IsScalarTower.algebraMap_apply A κ T]
      exact j.range.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have hgS : MvPolynomial.aeval z g ∈ S := by
    apply Algebra.adjoin_mono (Set.subset_insert _ _)
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (MvPolynomial.aeval z).mem_range_self g
  let s : AdjoinRoot FK := AdjoinRoot.of FK (MvPolynomial.map (algebraMap A κ) g)
  have hjs : j s = t (MvPolynomial.aeval z g) := by
    change j (AdjoinRoot.of FK (MvPolynomial.map (algebraMap A κ) g)) = _
    rw [AdjoinRoot.liftAlgHom_of]
    exact congrArg (fun f => f g) hψmap
  obtain ⟨p, hp⟩ := ExpChar.exists κ
  obtain ⟨n, hn⟩ := exists_pow_eq_pow_of_expChar (A := A) (κ := κ) q e p
  have hrad' : ∀ x : T, ∃ m n : ℕ, ∃ y : AdjoinRoot FK, j y = (j s ^ m * x) ^ p ^ n := by
    intro x
    obtain ⟨m, hm⟩ := tensor_uniform_power_containment S j.range
      (MvPolynomial.aeval z g) hgS q e htS hrad x
    obtain ⟨y, hy⟩ := (j.mem_range).mp hm
    refine ⟨m, n, y, ?_⟩
    rw [hy, hjs, ← hn]
  have hbij := bijective_comp_of_radicial p j hj s hrad'
  let e₁ : (C →ₐ[A] κ) ≃ (T →ₐ[κ] κ) := AlgHom.liftEquiv A κ C κ
  have he₁ : ∀ (φ : C →ₐ[A] κ) (c : C), e₁ φ (t c) = φ c := by
    intro φ c
    change e₁ φ (1 ⊗ₜ c) = φ c
    exact one_smul κ (φ c)
  rw [← Nat.card_eq_of_bijective _ hbij]
  apply Nat.card_congr
  refine e₁.subtypeEquiv ?_
  intro φ
  rw [hjs, he₁]

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
