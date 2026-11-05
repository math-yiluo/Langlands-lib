import Langlands.GroupScheme.KostantRosenlicht.Surjective
import Langlands.Representation.Exponents.CentralStatement
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Jacobson.Ideal

/-! Finite-dimensional central-action decomposition over an arbitrary algebraically closed field.
The Artinian-algebra argument is adapted from Worker 23's published
`FiniteActionSpectrumProof`; it is generalized from the complex field here. -/

noncomputable section

open scoped IsMulCommutative

namespace Langlands.CentralDecomposition

universe uK uR uA uV

section Algebra

variable {K : Type uK} [Field K] [IsAlgClosed K]
  {R : Type uR} [CommRing R] [Algebra K R] [Module.Finite K R]

/-- Every maximal ideal of a finite-dimensional commutative scalar algebra is
the kernel of a scalar character. -/
theorem exists_algHom_ker_eq (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[K] K, RingHom.ker φ = m := by
  have : Module.Finite K (R ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  have : Algebra.IsIntegral K (R ⧸ m) := Algebra.IsIntegral.of_finite K _
  let e : K ≃ₐ[K] R ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ m))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨(e.symm : R ⧸ m →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

omit [IsAlgClosed K] in
/-- A finite-dimensional commutative scalar algebra has finitely many scalar
characters. -/
theorem finite_algHom : Finite (R →ₐ[K] K) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : Finite {I : Ideal R // I.IsMaximal} :=
    (IsArtinianRing.setOfPred_isMaximal_finite R).to_subtype
  refine Finite.of_injective
    (fun φ : R →ₐ[K] K => (⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ
      (fun c => ⟨algebraMap K R c, by simp⟩)⟩ : {I : Ideal R // I.IsMaximal})) ?_
  intro φ ψ hφψ
  exact Langlands.GroupScheme.KostantRosenlicht.algHom_eq_of_ker_eq (congrArg Subtype.val hφψ)

omit [Module.Finite K R] [IsAlgClosed K] in
/-- Two distinct scalar characters are separated by an element. -/
theorem exists_separating (φ ψ : R →ₐ[K] K) (h : φ ≠ ψ) :
    ∃ r : R, φ r = 1 ∧ ψ r = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, φ s ≠ ψ s := by
    by_contra! H
    exact h (AlgHom.ext H)
  refine ⟨(φ s - ψ s)⁻¹ • (s - algebraMap K R (ψ s)), ?_, ?_⟩
  · simp only [map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hs)
  · simp

/-- Uniform decomposition data: elements whose sum is a unit and which are
annihilated by a fixed power of the corresponding character kernel. -/
theorem exists_decomposition [Fintype (R →ₐ[K] K)] :
    ∃ (N : ℕ) (h : (R →ₐ[K] K) → R),
      IsUnit (∑ φ, h φ) ∧ ∀ φ, ∀ y ∈ RingHom.ker φ ^ N, y * h φ = 0 := by
  classical
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  let J : Ideal R := ⨅ φ : R →ₐ[K] K, RingHom.ker φ
  have hJ : J ≤ Ideal.jacobson ⊥ := by
    refine le_sInf ?_
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (K := K) m
    rw [← hφ]
    exact iInf_le _ φ
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hN' : Ideal.jacobson (⊥ : Ideal R) ^ (N + 1) = ⊥ := by
    rw [pow_succ, hN, zero_mul]
    rfl
  choose r hr using fun (φ ψ : R →ₐ[K] K) (h : φ ≠ ψ) => exists_separating φ ψ h
  let g : (R →ₐ[K] K) → R := fun φ => ∏ ψ : {ψ // ψ ≠ φ}, r φ ψ ψ.2.symm
  have hg_self : ∀ φ : R →ₐ[K] K, φ (g φ) = 1 := by
    intro φ
    simp only [g, map_prod]
    exact Finset.prod_eq_one fun ψ _ => (hr φ ψ ψ.2.symm).1
  have hg_other : ∀ φ ψ : R →ₐ[K] K, ψ ≠ φ → ψ (g φ) = 0 := by
    intro φ ψ hψ
    simp only [g, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨ψ, hψ⟩) (hr φ ψ hψ.symm).2
  refine ⟨N + 1, fun φ => g φ ^ (N + 1), ?_, ?_⟩
  · have hmem : (∑ φ, g φ ^ (N + 1)) - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
      apply hJ
      rw [Submodule.mem_iInf]
      intro ψ
      rw [RingHom.mem_ker, map_sub, map_one, map_sum, Finset.sum_eq_single ψ]
      · rw [map_pow, hg_self, one_pow, sub_self]
      · intro φ _ hφ
        rw [map_pow, hg_other φ ψ (Ne.symm hφ), zero_pow (Nat.succ_ne_zero N)]
      · intro hψ
        exact absurd (Finset.mem_univ ψ) hψ
    simpa using (Ideal.mem_jacobson_bot.mp hmem) 1
  · intro φ y hy
    have h1 : RingHom.ker φ * Ideal.span {g φ} ≤ J := by
      rw [Ideal.mul_le]
      intro x hx z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [Submodule.mem_iInf]
      intro ψ
      rw [RingHom.mem_ker] at hx ⊢
      by_cases hψ : ψ = φ
      · subst hψ
        simp [hx]
      · simp [hg_other φ ψ hψ]
    have h2 : y * g φ ^ (N + 1) ∈ (RingHom.ker φ * Ideal.span {g φ}) ^ (N + 1) := by
      rw [mul_pow]
      exact Ideal.mul_mem_mul hy (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
    have h3 := Ideal.pow_right_mono (h1.trans hJ) (N + 1) h2
    rw [hN'] at h3
    exact (Submodule.mem_bot R).mp h3

end Algebra

section FiniteAction

variable {K : Type uK} [Field K] [IsAlgClosed K]
  {A : Type uA} [CommGroup A] {V : Type uV} [AddCommGroup V] [Module K V]

/-- The scalar character induced by a character of the operator algebra. -/
def algebraCharacter {B : Type*} [CommRing B] [Algebra K B]
    (τ : A →* B) (φ : B →ₐ[K] K) : A →* Kˣ :=
  (φ.toRingHom.toMonoidHom.comp τ).toHomUnits

omit [IsAlgClosed K] in
@[simp] theorem algebraCharacter_apply {B : Type*} [CommRing B] [Algebra K B]
    (τ : A →* B) (φ : B →ₐ[K] K) (a : A) :
    (algebraCharacter τ φ a : K) = φ (τ a) := rfl

/-- A finite-dimensional action is spanned by character spaces with one exponent
for every group element. No topology is assumed in this algebraic lemma. -/
theorem finite_action_spanning [Module.Finite K V] (τ : Representation K A V) :
    (⨆ (χ : A →* Kˣ) (n : ℕ),
      ⨅ a : A, Module.End.genEigenspace (τ a) (χ a : K) n) = ⊤ := by
  classical
  let B : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range τ)
  have hpair : (Set.range τ).Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    exact (Commute.all a b).map τ
  let : IsMulCommutative B := Algebra.isMulCommutative_adjoin K hpair
  let : CommRing B := inferInstance
  let τ' : A →* B := τ.codRestrict B (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
  let ι : B →ₐ[K] Module.End K V := B.val
  have hι : ∀ a, ι (τ' a) = τ a := fun _ => rfl
  let : Finite (B →ₐ[K] K) := finite_algHom (K := K) (R := B)
  let : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  obtain ⟨N, h, hu, hann⟩ := exists_decomposition (K := K) (R := B)
  let w : B := ((hu.unit⁻¹ : Bˣ) : B)
  have hdecomp : ∀ v : V, v = ∑ φ, ι (h φ) (ι w v) := by
    intro v
    have h1 : (∑ φ, h φ) * w = 1 := hu.mul_val_inv
    calc v = ι ((∑ φ, h φ) * w) v := by rw [h1, map_one, Module.End.one_apply]
         _ = ∑ φ, ι (h φ) (ι w v) := by
           rw [map_mul, Module.End.mul_apply, map_sum, LinearMap.sum_apply]
  rw [eq_top_iff]
  intro v _
  rw [hdecomp v]
  apply Submodule.sum_mem
  intro φ _
  apply Submodule.mem_iSup_of_mem (algebraCharacter τ' φ)
  apply Submodule.mem_iSup_of_mem N
  simp only [Submodule.mem_iInf]
  intro a
  apply Module.End.mem_genEigenspace_nat.mpr
  have hdef : τ a - (algebraCharacter τ' φ a : K) • 1 =
      ι (τ' a - algebraMap K B (φ (τ' a))) := by
    rw [map_sub, AlgHom.commutes, hι, Algebra.algebraMap_eq_smul_one,
      algebraCharacter_apply]
  have hker : τ' a - algebraMap K B (φ (τ' a)) ∈ RingHom.ker φ := by
    simp [RingHom.mem_ker]
  rw [LinearMap.mem_ker, hdef, ← map_pow, ← Module.End.mul_apply, ← map_mul,
    hann φ _ (Ideal.pow_mem_pow hker N), map_zero, LinearMap.zero_apply]

end FiniteAction

end Langlands.CentralDecomposition
