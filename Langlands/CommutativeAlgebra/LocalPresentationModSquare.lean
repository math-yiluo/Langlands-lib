import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Polynomial presentations of local algebras modulo the square of the maximal ideal -/

universe u v

open IsLocalRing

namespace Langlands.CommutativeAlgebra.LocalPresentationModSquare

/-- A local Noetherian `R`-algebra `A` with a surjection onto a field of finite type over
`R` receives a map from a polynomial ring in finitely many variables over `R` that is
surjective modulo the square of the maximal ideal of `A`. -/
theorem exists_mvPolynomial_surjective_mod_sq {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [Algebra.FiniteType R K]
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra R A]
    (ε : A →ₐ[R] K) (hε : Function.Surjective ε) :
    ∃ (ι : Type u) (_ : Fintype ι) (σA : MvPolynomial ι R →ₐ[R] A),
      ∀ a, ∃ s, a - σA s ∈ maximalIdeal A ^ 2 := by
  classical
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  choose aK haK using fun i : Fin n => hε (ψ (MvPolynomial.X i))
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal A))
  let v : ULift.{u} (Fin n ⊕ Fin k) → A := fun i => Sum.elim aK g i.down
  let σA : MvPolynomial (ULift.{u} (Fin n ⊕ Fin k)) R →ₐ[R] A := MvPolynomial.aeval v
  refine ⟨ULift.{u} (Fin n ⊕ Fin k), inferInstance, σA, ?_⟩
  -- the residue map of `σA` is surjective
  have hres : ∀ a : A, ∃ s, ε (σA s) = ε a := by
    intro a
    obtain ⟨p, hp⟩ := hψ (ε a)
    refine ⟨MvPolynomial.rename (fun i => ULift.up (Sum.inl i)) p, ?_⟩
    have : ε.comp (σA.comp (MvPolynomial.rename fun i => ULift.up (Sum.inl i))) = ψ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [σA, v, haK]
    rw [← hp, ← this]
    rfl
  have hker : ∀ a, ε a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε, RingHom.mem_ker]
    rfl
  intro a
  obtain ⟨s₀, hs₀⟩ := hres a
  have hm : a - σA s₀ ∈ maximalIdeal A := by
    rw [← hker, map_sub, hs₀, sub_self]
  rw [← hg] at hm
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hm
  choose sc hsc using fun l => hres (c l)
  refine ⟨s₀ + ∑ l, sc l * MvPolynomial.X (ULift.up (Sum.inr l)), ?_⟩
  have hσX : ∀ l, σA (MvPolynomial.X (ULift.up (Sum.inr l))) = g l := by
    intro l; simp [σA, v]
  have : a - σA (s₀ + ∑ l, sc l * MvPolynomial.X (ULift.up (Sum.inr l))) =
      ∑ l, (c l - σA (sc l)) * g l := by
    rw [map_add, map_sum]
    simp only [map_mul, hσX, sub_mul, Finset.sum_sub_distrib]
    simp only [smul_eq_mul] at hc
    rw [hc]
    ring
  rw [this, pow_two]
  refine Submodule.sum_mem _ fun l _ => Ideal.mul_mem_mul ?_ ?_
  · rw [← hker, map_sub, hsc l, sub_self]
  · rw [← hg]; exact Submodule.subset_span ⟨l, rfl⟩

end Langlands.CommutativeAlgebra.LocalPresentationModSquare
