import Langlands.CommutativeAlgebra.GradedLineLocal
import Mathlib.RingTheory.LocalRing.Module

/-! # Flat graded lines over arbitrary local rings -/

noncomputable section

universe u

open Polynomial

namespace Langlands.CommutativeAlgebra.GradedLine

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {c : A →+* LaurentPolynomial A} (hc : IsGrading R c)

/-- Each homogeneous component is a retract of the graded algebra, so
flatness of the algebra implies flatness of every component. -/
theorem flat_homog [Module.Flat R A] (n : ℤ) :
    Module.Flat R (homog hc n) := by
  let p : A →ₗ[R] homog hc n := (comp hc n).codRestrict _ (comp_mem_homog hc n)
  refine Module.Flat.of_retract (homog hc n).subtype p ?_
  ext a
  exact comp_self hc a.property

/-- In a positive degree, a power span in that degree has just one generator. -/
theorem powSpan_mul_eq_span {d : ℕ} (hd : 0 < d) (x : A) (j : ℕ) :
    powSpan (R := R) x d ((j : ℤ) * d) = Submodule.span R {x ^ j} := by
  unfold powSpan
  congr 1
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k = j := by
      have hd' : (d : ℤ) ≠ 0 := by omega
      exact_mod_cast (mul_left_inj' hd').mp hk
    simp [hk']
  · rintro rfl
    exact ⟨j, rfl, rfl⟩

/-- Taking a homogeneous component of evaluation isolates one polynomial coefficient. -/
theorem comp_aeval {d : ℕ} (hd : 0 < d) {x : A} (hx : x ∈ homog hc d)
    (f : R[X]) (j : ℕ) :
    comp hc ((j : ℤ) * d) (Polynomial.aeval x f) = f.coeff j • x ^ j := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, Polynomial.coeff_add, add_smul]
  | monomial k r =>
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul,
      comp_of_mem hc (pow_mem_homog hc hx k), Polynomial.coeff_monomial]
    by_cases h : k = j
    · subst h
      simp
    · have hdeg : ¬ ((j : ℤ) * d = (k : ℤ) * d) := by
        intro heq
        have hd' : (d : ℤ) ≠ 0 := by omega
        have hkj : j = k := by exact_mod_cast (mul_left_inj' hd').mp heq
        exact h hkj.symm
      simp [h, hdeg]

variable [IsLocalRing R]
  (hneg : ∀ a, ∀ n < 0, (c a).coeff n = 0)
  (hzero : ∀ a, (c a).coeff 0 ∈ Set.range (algebraMap R A))

include hneg hzero in
/-- A finite type flat connected positively graded algebra over a local ring
is a polynomial ring when its closed fibre is a graded line.
The local ring may have nilpotents. -/
theorem exists_aeval_bijective_of_flat [Algebra.FiniteType R A] [Module.Flat R A]
    {d : ℕ} (hd : 0 < d)
    {ψ : A →ₐ[R] (IsLocalRing.ResidueField R)[X]}
    (hψ : IsFibreLine hc (IsLocalRing.ResidueField R) d ψ)
    (hker : ∀ a, ψ a = 0 → a ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
    ∃ x ∈ homog hc d, Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hψ.exists_coeff_one_ne_zero
  let x := comp hc d a₀
  have hx : x ∈ homog hc d := comp_mem_homog hc d a₀
  have hle := homog_le_powSpan hc hneg hzero hψ hd hker hx ha₀
  have hxψ : ψ x ≠ 0 := by
    intro h
    exact ha₀ (by rw [show ψ (comp hc d a₀) = 0 from h, Polynomial.coeff_zero])
  have hfaithful (j : ℕ) : FaithfulSMul R (homog hc ((j : ℤ) * d)) := by
    let M := homog hc ((j : ℤ) * d)
    have hne : (⟨x ^ j, pow_mem_homog hc hx j⟩ : M) ≠ 0 := by
      intro h
      have hzero : x ^ j = 0 := congrArg Subtype.val h
      have hmap := congrArg ψ hzero
      rw [map_pow, map_zero] at hmap
      exact pow_ne_zero j hxψ hmap
    let : Nontrivial M := nontrivial_of_ne _ _ hne
    let : Module.Finite R M := Module.Finite.of_fg (homog_fg hc hneg hzero _)
    let : Module.Flat R M := flat_homog hc _
    let : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact inferInstance
  refine ⟨x, hx, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    ext j
    rw [Polynomial.coeff_zero]
    let M := homog hc ((j : ℤ) * d)
    let : FaithfulSMul R M := hfaithful j
    have heq : homog hc ((j : ℤ) * d) = Submodule.span R {x ^ j} := by
      refine le_antisymm ?_ (Submodule.span_le.2 (Set.singleton_subset_iff.2
        (pow_mem_homog hc hx j)))
      simpa only [powSpan_mul_eq_span hd] using hle ((j : ℤ) * d)
    have hfx : f.coeff j • x ^ j = 0 := by
      rw [← comp_aeval hc hd hx f j, hf, map_zero]
    apply eq_of_smul_eq_smul (α := M)
    intro a
    apply Subtype.ext
    change f.coeff j • (a : A) = (0 : R) • (a : A)
    rw [zero_smul]
    have ha : (a : A) ∈ homog hc ((j : ℤ) * d) := a.property
    rw [heq] at ha
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 ha
    rw [← hr, smul_smul, mul_comm, ← smul_smul, hfx, smul_zero]
  · intro a
    have hmem : a ∈ (Polynomial.aeval x : R[X] →ₐ[R] A).range := by
      rw [← sum_comp hc a]
      refine Subalgebra.sum_mem _ fun n _ => ?_
      have hspan : powSpan x d n ≤
          Subalgebra.toSubmodule (Polynomial.aeval x : R[X] →ₐ[R] A).range := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨j, -, rfl⟩
        exact ⟨X ^ j, by simp⟩
      exact hspan (hle n (comp_mem_homog hc n a))
    exact hmem

include hneg hzero in
/-- A universal graded line over the closed residue field suffices when the
graded algebra is flat over the local ring. -/
theorem exists_aeval_bijective_of_flat_of_universal
    [Algebra.FiniteType R A] [Module.Flat R A] {d : ℕ} (hd : 0 < d)
    {ψ : A →ₐ[R] (IsLocalRing.ResidueField R)[X]}
    (hu : IsUniversalLine (IsLocalRing.ResidueField R) ψ)
    (hg : ∀ (n : ℤ) (a : A), a ∈ homog hc n →
      ∀ j : ℕ, (j : ℤ) * d ≠ n → (ψ a).coeff j = 0) :
    ∃ x ∈ homog hc d, Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] A) :=
  exists_aeval_bijective_of_flat hc hneg hzero hd ⟨hg, hu.X_mem_span⟩ hu.ker_le

/-- A chosen polynomial-coordinate equivalence for a flat graded line over a local ring. -/
def polynomialEquivOfFlatOfUniversal
    [Algebra.FiniteType R A] [Module.Flat R A] {d : ℕ} (hd : 0 < d)
    {ψ : A →ₐ[R] (IsLocalRing.ResidueField R)[X]}
    (hu : IsUniversalLine (IsLocalRing.ResidueField R) ψ)
    (hg : ∀ (n : ℤ) (a : A), a ∈ homog hc n →
      ∀ j : ℕ, (j : ℤ) * d ≠ n → (ψ a).coeff j = 0) : R[X] ≃ₐ[R] A :=
  let hex := exists_aeval_bijective_of_flat_of_universal hc hneg hzero hd hu hg
  AlgEquiv.ofBijective (Polynomial.aeval (Classical.choose hex)) (Classical.choose_spec hex).2

end Langlands.CommutativeAlgebra.GradedLine
