import Langlands.RingTheory.Smooth.SectionJetCoordinates
import Langlands.RingTheory.Smooth.SectionJetIsomorphismLocus

/-! # Surjectivity of polynomial coordinates on section jets -/

noncomputable section

universe u v w

namespace Algebra.SectionJet.Coordinates

open MvPolynomial
open Langlands.GroupScheme.CoordinateWeights

/-- The polynomial augmentation sets every variable to zero. -/
abbrev polynomialAugmentation (σ : Type w) (R : Type u) [CommRing R] :
    MvPolynomial σ R →ₐ[R] R :=
  aeval fun _ => (0 : R)

theorem ker_polynomialAugmentation (σ : Type w) (R : Type u) [CommRing R] :
    RingHom.ker (polynomialAugmentation σ R) = idealOfVars σ R := by
  ext p
  rw [RingHom.mem_ker, Langlands.GroupScheme.TorusUnipotence.mem_idealOfVars_iff]
  rw [show polynomialAugmentation σ R p = constantCoeff p from
    augmentation_aeval (ε := AlgHom.id R R) (fun _ => 0) (fun _ => rfl) p]

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ε : A →ₐ[R] R} {σ : Type w} (z : σ → A)

theorem aeval_preserves_augmentation (hz : ∀ i, ε (z i) = 0) :
    ε.comp (aeval z) = polynomialAugmentation σ R := by
  ext i
  simp [polynomialAugmentation, hz]

private theorem exists_polynomial_approximation_sq (hz : ∀ i, ε (z i) = 0)
    (hspan : Submodule.span R (Set.range (AugmentedAlgebra.classMap ε ∘ z)) = ⊤)
    {x : A} (hx : x ∈ RingHom.ker ε) :
    ∃ p : MvPolynomial σ R, x - aeval z p ∈ RingHom.ker ε ^ 2 := by
  rw [← Finsupp.range_linearCombination, LinearMap.range_eq_top] at hspan
  obtain ⟨c, hc⟩ := hspan (AugmentedAlgebra.classMap ε x)
  let a := Finsupp.linearCombination R z c
  have ha : a ∈ RingHom.ker ε := by
    change ε.toLinearMap (Finsupp.linearCombination R z c) = 0
    rw [Finsupp.apply_linearCombination, show ε.toLinearMap ∘ z = 0 from funext hz]
    simp
  have hclass : AugmentedAlgebra.classMap ε a = AugmentedAlgebra.classMap ε x := by
    rw [show a = Finsupp.linearCombination R z c from rfl, Finsupp.apply_linearCombination]
    exact hc
  refine ⟨Finsupp.linearCombination R X c, ?_⟩
  have heval : aeval z (Finsupp.linearCombination R (X : σ → MvPolynomial σ R) c) = a := by
    rw [← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination,
      show ⇑(aeval z : MvPolynomial σ R →ₐ[R] A).toLinearMap ∘ X = z from
        funext fun i => by simp]
  rw [heval]
  have hsub : x - a ∈ RingHom.ker ε := Ideal.sub_mem _ hx ha
  have hzero : (RingHom.ker ε).toCotangent ⟨x - a, hsub⟩ = 0 := by
    calc
      _ = AugmentedAlgebra.classMap ε (x - a) :=
        (AugmentedAlgebra.classMap_ideal ε ⟨x - a, hsub⟩).symm
      _ = 0 := by rw [map_sub, hclass, sub_self]
  rwa [Ideal.toCotangent_eq_zero] at hzero

private theorem exists_polynomial_approximation_succ
    (hfirst : ∀ x ∈ RingHom.ker ε, ∃ p : MvPolynomial σ R, x - aeval z p ∈ RingHom.ker ε ^ 2)
    (m : ℕ) {x : A} (hx : x ∈ RingHom.ker ε ^ m) :
    ∃ p : MvPolynomial σ R, x - aeval z p ∈ RingHom.ker ε ^ (m + 1) := by
  induction m generalizing x with
  | zero =>
    refine ⟨C (ε x), ?_⟩
    rw [zero_add, pow_one, aeval_C, RingHom.mem_ker, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  | succ m ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨p, hp⟩ := ih ha
      obtain ⟨q, hq⟩ := hfirst b hb
      have hval : aeval z p ∈ RingHom.ker ε ^ m := by
        rw [show aeval z p = a - (a - aeval z p) by ring]
        exact Ideal.sub_mem _ ha (Ideal.pow_le_pow_right (Nat.le_succ m) hp)
      refine ⟨p * q, ?_⟩
      rw [show a * b - aeval z (p * q) =
        (a - aeval z p) * b + aeval z p * (b - aeval z q) by rw [map_mul]; ring]
      apply Ideal.add_mem
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hp hb
      · rw [show m + 1 + 1 = m + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hval hq
    · rintro a b ⟨p, hp⟩ ⟨q, hq⟩
      refine ⟨p + q, ?_⟩
      rw [show a + b - aeval z (p + q) =
        (a - aeval z p) + (b - aeval z q) by rw [map_add]; ring]
      exact Ideal.add_mem _ hp hq

/-- Augmentation-ideal lifts of conormal generators give surjections from
the polynomial section jets at every order. -/
def SectionJetPolynomialSurjectivityStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (σ : Type w) [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (z : σ → A) (hz : ∀ i, ε (z i) = 0),
    Submodule.span R (Set.range (AugmentedAlgebra.classMap ε ∘ z)) = ⊤ →
      ∀ n : ℕ, Function.Surjective (jetMap (aeval_preserves_augmentation z hz) n)

theorem sectionJetPolynomialSurjectivity : SectionJetPolynomialSurjectivityStatement.{u, v, w} := by
  intro R A σ _ _ _ ε z hz hspan n y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  suffices h : ∀ m : ℕ, ∃ p : MvPolynomial σ R, a - aeval z p ∈ RingHom.ker ε ^ m by
    obtain ⟨p, hp⟩ := h (n + 1)
    refine ⟨Ideal.Quotient.mk _ p, ?_⟩
    rw [jetMap_mk, Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
    exact hp
  intro m
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_polynomial_approximation_succ z
      (fun _ hx => exists_polynomial_approximation_sq z hz hspan hx) m hp
    exact ⟨p + q, by rwa [map_add, ← sub_sub]⟩

end Algebra.SectionJet.Coordinates
