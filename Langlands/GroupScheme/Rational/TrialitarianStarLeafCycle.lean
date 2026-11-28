import Langlands.GroupScheme.SimplyConnected.TypeDRankOneOrbit
import Mathlib.FieldTheory.Galois.Basic

/-! # The cyclic star action on the leaves of a trialitarian index split by a cubic field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem fin4_leafCycle_values :
    ∀ a b c : Fin 4, Function.Injective ![a, 1, b, c] →
      ![a, 1, b, c] (![a, 1, b, c] a) = 0 →
      ![a, 1, b, c] (![a, 1, b, c] b) = 2 →
      ![a, 1, b, c] (![a, 1, b, c] c) = 3 → a ≠ 0 →
      (a = 2 ∧ b = 3 ∧ c = 0) ∨ (a = 3 ∧ c = 2 ∧ b = 0) := by
  decide

/-- A permutation of `Fin 4` fixing `1`, of order dividing three and moving `0`, is one of the
two three-cycles of the leaves `0, 2, 3`. -/
theorem fin4_leafCycle (π : Fin 4 → Fin 4) (hinj : Function.Injective π) (h1 : π 1 = 1)
    (h3 : ∀ i, π (π (π i)) = i) (h0 : π 0 ≠ 0) :
    (π 0 = 2 ∧ π 2 = 3 ∧ π 3 = 0) ∨ (π 0 = 3 ∧ π 3 = 2 ∧ π 2 = 0) := by
  have hπ : π = ![π 0, 1, π 2, π 3] := by
    funext i
    fin_cases i <;> simp [h1]
  have key := fin4_leafCycle_values (π 0) (π 2) (π 3) (hπ ▸ hinj)
    (by rw [← hπ]; exact h3 0) (by rw [← hπ]; exact h3 2) (by rw [← hπ]; exact h3 3) h0
  exact key

/-- In a group of order three every nontrivial element generates, has order three, and is
distinct from its square. -/
theorem card_three_generator {Γ : Type*} [Group Γ] [Finite Γ] (hcard : Nat.card Γ = 3)
    (σ : Γ) (hσ : σ ≠ 1) :
    (∀ ρ : Γ, ∃ n : ℕ, ρ = σ ^ n) ∧ σ ^ 3 = 1 ∧ (1 : Γ) ≠ σ ∧ (1 : Γ) ≠ σ ^ 2 ∧ σ ≠ σ ^ 2 := by
  have h3 : σ ^ 3 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'

  have hord : orderOf σ = 3 := by
    have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ
    · exact h
  have hsq : σ ^ 2 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  refine ⟨?_, h3, fun h => hσ h.symm, fun h => hsq h.symm, ?_⟩
  · intro ρ
    have hcyc : IsCyclic Γ := isCyclic_of_prime_card (p := 3) hcard
    have hgen : ∀ x : Γ, x ∈ Subgroup.zpowers σ := by
      intro x
      have hle : (Subgroup.zpowers σ) = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hord, hcard]
      rw [hle]
      exact Subgroup.mem_top x
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hgen ρ))
    exact ⟨n, hn.symm⟩
  · intro h
    have h1 : σ = 1 := by
      have : σ ^ 2 = σ ^ 1 * σ := by group
      rw [this, pow_one] at h
      exact (mul_eq_left.mp h.symm)
    exact hσ h1

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- If the star action of a `D₄` index fixes no leaf and is trivial on the automorphisms
fixing a cubic Galois field `K`, then some generator `σ` of `Gal(K/F)`, with a lift `τ`, acts
by the three-cycle `0 ↦ 2 ↦ 3 ↦ 0` on the leaves. -/
theorem TitsIndexData.exists_star_leafCycle (d : TitsIndexData H) (q : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b))
    (hleaf : ∀ a : d.Vertex, q a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a)
    (K : Type u) [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [Algebra K (SeparableClosure F)] [IsScalarTower F K (SeparableClosure F)]
    (hK : Module.finrank F K = 3)
    (htriv : ∀ τ : SeparableClosure F ≃ₐ[F] SeparableClosure F,
      (∀ x : K, τ (algebraMap K (SeparableClosure F) x) = algebraMap K (SeparableClosure F) x) →
        ∀ a, d.star τ a = a) :
    ∃ (σ : K ≃ₐ[F] K) (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F),
      (∀ x : K, τ (algebraMap K (SeparableClosure F) x) =
        algebraMap K (SeparableClosure F) (σ x)) ∧ σ ≠ 1 ∧
      d.star τ (q.symm 0) = q.symm 2 ∧ d.star τ (q.symm 2) = q.symm 3 ∧
        d.star τ (q.symm 3) = q.symm 0 := by
  classical
  set E := SeparableClosure F
  have hcard : Nat.card (K ≃ₐ[F] K) = 3 := by
    rw [← hK]
    exact IsGalois.card_aut_eq_finrank F K
  obtain ⟨τ₀, hτ₀⟩ := hleaf (q.symm 0) (by simp)
  let σ₀ : K ≃ₐ[F] K := τ₀.restrictNormal K
  have hcomm (τ : E ≃ₐ[F] E) (x : K) :
      τ (algebraMap K E x) = algebraMap K E (τ.restrictNormal K x) :=
    (τ.restrictNormal_commutes K x).symm
  have hσ₀ : σ₀ ≠ 1 := by
    intro h
    apply hτ₀
    apply htriv τ₀
    intro x
    rw [hcomm, show τ₀.restrictNormal K = σ₀ from rfl, h]
    rfl
  obtain ⟨_, hσ3, _, _, _⟩ := card_three_generator hcard σ₀ hσ₀
  -- The numbered star permutation.
  let π : Fin 4 → Fin 4 := fun i => q (d.star τ₀ (q.symm i))
  have hπinj : Function.Injective π := by
    intro i j h
    have h1 := q.injective h
    have h2 := (d.starPermutation τ₀).injective h1
    exact q.symm.injective h2
  have hπ1 : π 1 = 1 := by
    change q (d.star τ₀ (q.symm 1)) = 1
    rw [d.star_fixes_center_of_D (by decide) q hD τ₀ (q.symm 1) (by simp)]
    simp
  have hπ3 : ∀ i, π (π (π i)) = i := by
    intro i
    have hτ3 : ∀ a, d.star (τ₀ ^ 3) a = a := by
      apply htriv
      intro x
      rw [hcomm]
      congr 1
      rw [show (τ₀ ^ 3).restrictNormal K = σ₀ ^ 3 from
        map_pow (AlgEquiv.restrictNormalHom K) τ₀ 3, hσ3]
      rfl
    have := hτ3 (q.symm i)
    rw [pow_succ, pow_two, d.star_mul, d.star_mul] at this
    simp only [π, Equiv.symm_apply_apply]
    rw [this, Equiv.apply_symm_apply]
  have hπ0 : π 0 ≠ 0 := by
    intro h
    apply hτ₀
    apply q.injective
    change π 0 = q (q.symm 0)
    rw [h, Equiv.apply_symm_apply]
  have hstar (τ : E ≃ₐ[F] E) (i j : Fin 4) (h : q (d.star τ (q.symm i)) = j) :
      d.star τ (q.symm i) = q.symm j := by
    rw [← h, Equiv.symm_apply_apply]
  rcases fin4_leafCycle π hπinj hπ1 hπ3 hπ0 with ⟨h0, h2, h3⟩ | ⟨h0, h3, h2⟩
  · exact ⟨σ₀, τ₀, hcomm τ₀, hσ₀, hstar τ₀ 0 2 h0, hstar τ₀ 2 3 h2, hstar τ₀ 3 0 h3⟩
  · refine ⟨σ₀ ^ 2, τ₀ ^ 2, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hcomm]
      congr 1
      rw [show (τ₀ ^ 2).restrictNormal K = σ₀ ^ 2 from
        map_pow (AlgEquiv.restrictNormalHom K) τ₀ 2]
    · intro h
      have := card_three_generator hcard σ₀ hσ₀
      exact this.2.2.2.1 h.symm
    · rw [pow_two, d.star_mul, hstar τ₀ 0 3 h0, hstar τ₀ 3 2 h3]
    · rw [pow_two, d.star_mul, hstar τ₀ 2 0 h2, hstar τ₀ 0 3 h0]
    · rw [pow_two, d.star_mul, hstar τ₀ 3 2 h3, hstar τ₀ 2 0 h2]

end Langlands.GroupScheme
