import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Commutative algebra for the valuative existence criterion

Ring-theoretic inputs to the descent step of the valuative existence criterion for
separated universally closed morphisms of algebraic spaces: common denominators in
`K ⊗[A] P`, flatness of torsion-free modules over a valuation ring, injectivity of
`M → K ⊗[A] M` for flat `M`, and a faithful flatness criterion over a local ring.
-/

noncomputable section

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence

section Denominators

variable {A K P : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing P] [Algebra A P]

/-- Every element of `K ⊗[A] P` has a nonzero common denominator in `A`. -/
theorem exists_smul_eq_one_tmul (t : K ⊗[A] P) :
    ∃ a : A, a ≠ 0 ∧ ∃ p : P, a • t = (1 : K) ⊗ₜ[A] p := by
  induction t using TensorProduct.inductionOn with
  | tmul k p =>
    obtain ⟨⟨n, d⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors A) k
    refine ⟨d, nonZeroDivisors.ne_zero d.2, n • p, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, Algebra.smul_def, mul_comm]
    simp only at hk
    rw [hk, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁, p₁, e₁⟩ := h₁
    obtain ⟨a₂, ha₂, p₂, e₂⟩ := h₂
    refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, a₂ • p₁ + a₁ • p₂, ?_⟩
    rw [smul_add, mul_comm a₁ a₂, mul_smul, e₁, mul_comm a₂ a₁, mul_smul, e₂,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]

/-- An `A`-algebra map from `K ⊗[A] P` to a `K`-algebra kills an ideal as soon as it kills
the elements of the ideal of the form `1 ⊗ p`. -/
theorem map_eq_zero_of_tmul {R : Type u} [CommRing R] [Algebra A R] [Algebra K R]
    [IsScalarTower A K R] (H : K ⊗[A] P →ₐ[A] R) (I : Ideal (K ⊗[A] P))
    (hI : ∀ p : P, (1 : K) ⊗ₜ[A] p ∈ I → H ((1 : K) ⊗ₜ[A] p) = 0) {t : K ⊗[A] P}
    (ht : t ∈ I) : H t = 0 := by
  obtain ⟨a, ha, p, e⟩ := exists_smul_eq_one_tmul (K := K) t
  have hmem : (1 : K) ⊗ₜ[A] p ∈ I := by
    rw [← e, Algebra.smul_def]
    exact I.mul_mem_left _ ht
  have h0 : a • H t = 0 := by
    rw [← map_smul, e]
    exact hI p hmem
  rw [← algebraMap_smul K a (H t)] at h0
  have hK : algebraMap A K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  exact (smul_eq_zero.mp h0).resolve_left hK

end Denominators

section Flatness

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- Over a valuation ring, a module embedding into a `K`-vector space is flat. -/
theorem flat_of_injective [ValuationRing A] {D B : Type u} [AddCommGroup D] [Module A D]
    [AddCommGroup B] [Module A B] [Module K B] [IsScalarTower A K B] (ι : D →ₗ[A] B)
    (hι : Function.Injective ι) : Module.Flat A D := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  rw [eq_bot_iff]
  intro d hd
  obtain ⟨a, had⟩ := (Submodule.mem_torsion_iff d).mp hd
  have h0 : (a : A) • ι d = 0 := by rw [← map_smul, ← Submonoid.smul_def, had, map_zero]
  rw [← algebraMap_smul K (a : A) (ι d)] at h0
  have hK : algebraMap A K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero a.2)
  have : ι d = 0 := (smul_eq_zero.mp h0).resolve_left hK
  rw [Submodule.mem_bot]
  exact hι (this.trans (map_zero ι).symm)

omit [IsDomain A] in
/-- For a flat `A`-algebra `M`, the map `M → K ⊗[A] M` is injective. -/
theorem includeRight_injective (M : Type u) [CommRing M] [Algebra A M] [Module.Flat A M] :
    Function.Injective (Algebra.TensorProduct.includeRight : M →ₐ[A] K ⊗[A] M) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (Algebra.linearMap A K) (IsFractionRing.injective A K)
  have heq : ⇑(Algebra.TensorProduct.includeRight : M →ₐ[A] K ⊗[A] M) =
      (LinearMap.rTensor M (Algebra.linearMap A K)) ∘ (TensorProduct.lid A M).symm := by
    funext m
    simp [Algebra.TensorProduct.includeRight_apply]
  rw [heq]
  exact h.comp (TensorProduct.lid A M).symm.injective

end Flatness

section FaithfulFlatness

variable {A D : Type u} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D]

/-- Over a local ring, a flat algebra whose extended maximal ideal is proper is faithfully
flat. -/
theorem faithfullyFlat_of_map_maximalIdeal_ne_top [Module.Flat A D]
    (h : (IsLocalRing.maximalIdeal A).map (algebraMap A D) ≠ ⊤) :
    Module.FaithfullyFlat A D := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop => h ?_⟩
  have hle : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hI
  rw [Ideal.smul_top_eq_map] at htop
  rw [eq_top_iff]
  have h1 : (1 : D) ∈ I.map (algebraMap A D) := by
    have := congrArg (fun N : Submodule A D => (1 : D) ∈ N) htop
    simp only [Submodule.restrictScalars_mem, Submodule.mem_top, eq_iff_iff, iff_true] at this
    exact this
  intro x _
  have h2 : (1 : D) ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A D) :=
    Ideal.map_mono hle h1
  simpa using Ideal.mul_mem_left _ x h2

end FaithfulFlatness

end Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence
