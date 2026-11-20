import Langlands.Algebra.ProjectiveTensorCoefficients
import Langlands.RingTheory.Smooth.SectionJetBaseChange
import Mathlib.RingTheory.Filtration

/-! # The closed base locus for a closed subscheme to contain a section neighborhood -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Algebra.SectionJet

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  (ε : A →ₐ[R] R) (J : Ideal A)
  (B : Type w) [CommRing B] [Algebra R B]

/-- The extension of the closed subscheme's ideal to the scalar-extended algebra. -/
abbrev extendedIdeal : Ideal (B ⊗[R] A) :=
  J.map (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom

/-- The equations on the base for the closed subscheme to contain every jet of the section. -/
def neighborhoodIdeal : Ideal R :=
  ⨆ n : ℕ, coefficientIdeal
    ((fun a : A => (1 : R) ⊗ₜ[R] (Ideal.Quotient.mk _ a : Quotient ε n)) '' (J : Set A))

/-- Vanishing of the base equations is equivalent to containment of the actual section jets
after scalar extension. -/
theorem neighborhoodIdeal_le_ker_iff_powers [Smooth R A] :
    neighborhoodIdeal ε J ≤ RingHom.ker (algebraMap R B) ↔
      ∀ n : ℕ, extendedIdeal J B ≤ RingHom.ker (baseChangeAugmentation ε B) ^ (n + 1) := by
  unfold neighborhoodIdeal
  simp only [iSup_le_iff]
  apply forall_congr'
  intro n
  rw [show algebraMap R B = (Algebra.ofId R B).toRingHom from rfl,
    coefficientIdeal_le_ker_iff _ (Algebra.ofId R B),
    extendedIdeal, Ideal.map_le_iff_le_comap]
  constructor
  · intro h x hx
    have hzero := h _ ⟨x, hx, rfl⟩
    rw [LinearMap.rTensor_tmul] at hzero
    have hz := congrArg (baseChangeEquiv ε B n) hzero
    rw [show (Algebra.ofId R B).toLinearMap 1 = 1 from map_one (Algebra.ofId R B),
      baseChangeEquiv_tmul_mk, map_zero] at hz
    change (1 : B) ⊗ₜ[R] x ∈ RingHom.ker (baseChangeAugmentation ε B) ^ (n + 1)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [LinearMap.rTensor_tmul, show (Algebra.ofId R B).toLinearMap 1 = 1 from
      map_one (Algebra.ofId R B)]
    apply (baseChangeEquiv ε B n).injective
    rw [baseChangeEquiv_tmul_mk, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h ha)

private theorem exists_annihilator_of_le_powers {C : Type*} [CommRing C] [IsNoetherianRing C]
    (I K : Ideal C) (h : ∀ n : ℕ, K ≤ I ^ (n + 1)) :
    ∃ d : C, 1 - d ∈ I ∧ d ∈ (K : Submodule C C).annihilator := by
  have hp (n : ℕ) : (K : Submodule C C) ≤ I ^ n • (⊤ : Submodule C C) := by
    rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    cases n with
    | zero => simp
    | succ n => exact h n
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (K : Submodule C C)
  have hle : (K : Submodule C C) ≤ I • (K : Submodule C C) := by
    have he := hk (k + 1) k.le_succ
    rw [inf_eq_right.mpr (hp (k + 1)), inf_eq_right.mpr (hp k),
      show k + 1 - k = 1 by omega, pow_one] at he
    exact he.le
  obtain ⟨r, hr, hfix⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    I (K : Submodule C C) K.fg_of_isNoetherianRing hle
  exact ⟨1 - r, by simpa, Submodule.mem_annihilator.mpr
    (fun x hx => by rw [sub_smul, one_smul, hfix x hx, sub_self])⟩

/-- A principal neighborhood containing the whole section lies in the closed subscheme
if and only if the map on the base kills the coefficient ideal. The test algebra is arbitrary. -/
def SectionJetNeighborhoodStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsNoetherianRing R] [Smooth R A]
    (ε : A →ₐ[R] R) (J : Ideal A),
    neighborhoodIdeal ε J ≤ RingHom.ker (algebraMap R B) ↔
      ∃ d : B ⊗[R] A, baseChangeAugmentation ε B d = 1 ∧
        d ∈ (extendedIdeal J B : Submodule (B ⊗[R] A) (B ⊗[R] A)).annihilator

theorem sectionJetNeighborhood : SectionJetNeighborhoodStatement.{u, v, w} := by
  intro R A B _ _ _ _ _ _ _ ε J
  constructor
  · intro h
    let I := neighborhoodIdeal ε J
    let Q := R ⧸ I
    have hQ : I ≤ RingHom.ker (algebraMap R Q) := by
      change I ≤ RingHom.ker (Ideal.Quotient.mk I)
      rw [Ideal.mk_ker]
    have : IsNoetherianRing (Q ⊗[R] A) := Algebra.FiniteType.isNoetherianRing Q _
    obtain ⟨d, hd, hdJ⟩ := exists_annihilator_of_le_powers
      (RingHom.ker (baseChangeAugmentation ε Q)) (extendedIdeal J Q)
      ((neighborhoodIdeal_le_ker_iff_powers ε J Q).mp hQ)
    have hdε : baseChangeAugmentation ε Q d = 1 := by
      change baseChangeAugmentation ε Q (1 - d) = 0 at hd
      rw [map_sub, map_one, sub_eq_zero] at hd
      exact hd.symm
    let g : Q →ₐ[R] B := Ideal.Quotient.liftₐ I (Algebra.ofId R B) h
    let Φ := Algebra.TensorProduct.map g (AlgHom.id R A)
    have hε (x : Q ⊗[R] A) :
        baseChangeAugmentation ε B (Φ x) = g (baseChangeAugmentation ε Q x) := by
      induction x using TensorProduct.inductionOn with
      | tmul q a =>
        simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          baseChangeAugmentation_tmul, map_mul, AlgHom.commutes]
      | add x y hx hy => simp [hx, hy]
    have hmap : (extendedIdeal J Q).map Φ.toRingHom = extendedIdeal J B := by
      rw [extendedIdeal, extendedIdeal, Ideal.map_map]
      congr 1
      ext x
      change Φ (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] x
      simp [Φ]
    refine ⟨Φ d, by rw [hε, hdε, map_one], Submodule.mem_annihilator.mpr ?_⟩
    change extendedIdeal J B ≤ LinearMap.ker (LinearMap.mulLeft _ (Φ d))
    rw [← hmap, Ideal.map_le_iff_le_comap]
    intro x hx
    change Φ d * Φ x = 0
    rw [← map_mul, show d * x = 0 from Submodule.mem_annihilator.mp hdJ x hx, map_zero]
  · rintro ⟨d, hd, hJ⟩
    apply (neighborhoodIdeal_le_ker_iff_powers ε J B).mpr
    have hmem : 1 - d ∈ RingHom.ker (baseChangeAugmentation ε B) := by
      simp [RingHom.mem_ker, hd]
    intro n x hx
    have hfix : x * (1 - d) = x := by
      rw [mul_sub, mul_one, mul_comm x d,
        show d * x = 0 from Submodule.mem_annihilator.mp hJ x hx, sub_zero]
    change x ∈ RingHom.ker (baseChangeAugmentation ε B) ^ (n + 1)
    induction n with
    | zero =>
      rw [zero_add, pow_one, ← hfix]
      exact Ideal.mul_mem_left _ _ hmem
    | succ n ih =>
      rw [pow_succ]
      exact hfix ▸ Ideal.mul_mem_mul ih hmem

end Algebra.SectionJet
