import Mathlib
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.JacobianQuotient

/-! # A Jacobian criterion for polynomial rings over a formally smooth residue field -/

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open IsLocalRing MvPolynomial

variable {R₀ : Type*} [CommRing R₀] {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- First-order Taylor expansion: two algebra maps from a polynomial ring which agree modulo a
square-zero ideal differ by the derivative applied to the differences on the variables. -/
theorem algHom_sub_eq_sum_pderiv {E : Type*} [CommRing E] [Algebra R₀ E] (K : Ideal E)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = 0) (φ₁ φ₂ : MvPolynomial τ R₀ →ₐ[R₀] E)
    (hφ : ∀ v, φ₁ (X v) - φ₂ (X v) ∈ K) (p : MvPolynomial τ R₀) :
    φ₁ p - φ₂ p = ∑ v, φ₁ (pderiv v p) * (φ₁ (X v) - φ₂ (X v)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    ring
  | mul_X p w hp =>
    have hpK : φ₁ p - φ₂ p ∈ K := by
      rw [hp]
      exact Ideal.sum_mem _ fun v _ => Ideal.mul_mem_left _ _ (hφ v)
    have h0 := hK _ hpK _ (hφ w)
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_mul,
      Finset.sum_add_distrib]
    have h1 : ∑ v, φ₁ p * φ₁ (pderiv v (X w)) * (φ₁ (X v) - φ₂ (X v)) =
        φ₁ p * (φ₁ (X w) - φ₂ (X w)) := by
      rw [Finset.sum_eq_single w]
      · simp [pderiv_X]
      · intro v _ hv
        simp [pderiv_X, hv]
      · simp
    have h2 : ∑ v, φ₁ (X w) * φ₁ (pderiv v p) * (φ₁ (X v) - φ₂ (X v)) =
        φ₁ (X w) * (φ₁ p - φ₂ p) := by
      rw [hp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1, h2]
    linear_combination (-1 : E) * h0

/-- **Jacobian criterion.** Let `L` be a local algebra over the polynomial ring
`R₀[X_v, v ∈ τ]` whose residue field is formally smooth over `R₀`. If polynomials `g j` map into
the maximal ideal of `L` with linearly independent classes in the cotangent space, then their
gradients `(∂ g j / ∂ X_v)_v`, reduced to the residue field, are linearly independent. -/
theorem linearIndependent_pderiv_of_linearIndependent_cotangent
    {L : Type*} [CommRing L] [IsLocalRing L] [Algebra (MvPolynomial τ R₀) L] [Algebra R₀ L]
    [IsScalarTower R₀ (MvPolynomial τ R₀) L] [Algebra.FormallySmooth R₀ (ResidueField L)]
    {ι : Type*} [Fintype ι] (g : ι → MvPolynomial τ R₀)
    (hgm : ∀ j, algebraMap _ L (g j) ∈ maximalIdeal L)
    (hg : LinearIndependent (ResidueField L)
      (fun j => (maximalIdeal L).toCotangent ⟨_, hgm j⟩)) :
    LinearIndependent (ResidueField L)
      (fun j (v : τ) => residue L (algebraMap _ L (pderiv v (g j)))) := by
  classical
  set m := maximalIdeal L
  set κ := ResidueField L
  set E := L ⧸ m ^ 2
  have hm2 : ∀ x ∈ m ^ 2, IsScalarTower.toAlgHom R₀ L κ x = 0 := fun x hx =>
    (residue_eq_zero_iff x).mpr (Ideal.pow_le_self two_ne_zero hx)
  let π : E →ₐ[R₀] κ := Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R₀ L κ) hm2
  have hπ : ∀ x, π (Ideal.Quotient.mk _ x) = residue L x := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk _ x, hπ x⟩
  set K := RingHom.ker (π : E →+* κ)
  have hK : ∀ a ∈ K, ∀ b ∈ K, a * b = 0 := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [RingHom.mem_ker] at ha hb
    change π _ = 0 at ha hb
    rw [hπ, residue_eq_zero_iff] at ha hb
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul ha hb
  have hnil : IsNilpotent K := by
    refine ⟨2, ?_⟩
    rw [pow_two K, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [hK a ha b hb]
    exact zero_mem _
  let s : κ →ₐ[R₀] E := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R₀ κ) π hπs hnil
  have hs : ∀ y, π (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R₀ κ) π hπs hnil y
  let ι₀ := IsScalarTower.toAlgHom R₀ (MvPolynomial τ R₀) L
  let φ₁ : MvPolynomial τ R₀ →ₐ[R₀] E := (Ideal.Quotient.mkₐ R₀ (m ^ 2)).comp ι₀
  let φ₂ : MvPolynomial τ R₀ →ₐ[R₀] E := s.comp ((IsScalarTower.toAlgHom R₀ L κ).comp ι₀)
  have hφ₁ : ∀ p, φ₁ p = Ideal.Quotient.mk _ (algebraMap _ L p) := fun p => rfl
  have hφ₂ : ∀ p, φ₂ p = s (residue L (algebraMap _ L p)) := fun p => rfl
  have hφ : ∀ p, φ₁ p - φ₂ p ∈ K := by
    intro p
    rw [RingHom.mem_ker]
    change π (φ₁ p - φ₂ p) = 0
    rw [map_sub, hφ₁, hφ₂, hπ, hs, sub_self]
  have hgj : ∀ j, φ₁ (g j) = ∑ v, φ₁ (pderiv v (g j)) * (φ₁ (X v) - φ₂ (X v)) := by
    intro j
    rw [← algHom_sub_eq_sum_pderiv K hK φ₁ φ₂ (fun v => hφ _) (g j), hφ₂,
      (residue_eq_zero_iff _).mpr (hgm j), map_zero, sub_zero]
  have hlin := (linearIndependent_toCotangent_iff (fun j => algebraMap _ L (g j)) hgm).mp hg
  rw [Fintype.linearIndependent_iff]
  intro c hc
  choose a ha using fun j => residue_surjective (R := L) (c j)
  -- the combination `∑ aⱼ gⱼ` lies in `𝔪²`
  have hmem : ∑ j, a j * algebraMap _ L (g j) ∈ m ^ 2 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    simp_rw [map_mul, ← hφ₁, hgj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    have hev : ∑ j, Ideal.Quotient.mk (m ^ 2) (a j) * φ₁ (pderiv v (g j)) ∈ K := by
      rw [RingHom.mem_ker]
      change π _ = 0
      rw [map_sum]
      have := congrFun hc v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hπ, hφ₁, hπ, ha]
    have := hK _ hev _ (hφ (X v))
    rw [Finset.sum_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  intro j
  rw [← ha j]
  exact (residue_eq_zero_iff _).mpr (hlin a hmem j)

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
