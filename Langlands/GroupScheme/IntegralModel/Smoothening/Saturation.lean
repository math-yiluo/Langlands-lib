import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Algebra maps out of subalgebras of the generic fibre

Over a domain `R` with fraction field `K`, every element of `K ⊗[R] A` is
`s⁻¹ (1 ⊗ a)`. An algebra map `f : A → D` to a flat `R`-algebra extends to an
`R`-subalgebra `B` of `K ⊗[R] A` as soon as `f a` is divisible by `s` whenever
`s⁻¹ (1 ⊗ a)` lies in `B`, and the extension is unique. -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening

variable {R : Type u} {K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section Generic

variable (K) (D : Type v) [CommRing D] [Algebra R D]

/-- Every element of `K ⊗[R] D` becomes `1 ⊗ d` after multiplication by a
nonzero element of `R`. -/
theorem exists_smul_eq_one_tmul (x : K ⊗[R] D) :
    ∃ (s : R) (d : D), s ≠ 0 ∧ s • x = (1 : K) ⊗ₜ d := by
  obtain ⟨⟨d, s⟩, h⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K D 1) x
  exact ⟨s, d, nonZeroDivisors.ne_zero s.2, h⟩

omit [IsDomain R] in
/-- For a flat `R`-algebra the inclusion into the generic fibre is injective. -/
theorem includeRight_injective_of_flat [Module.Flat R D] :
    Function.Injective (Algebra.TensorProduct.includeRight : D →ₐ[R] K ⊗[R] D) :=
  Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)

omit [IsDomain R] in
/-- Multiplication by a nonzero scalar is injective on `K ⊗[R] D`. -/
theorem smul_left_cancel {s : R} (hs : s ≠ 0) {x y : K ⊗[R] D} (h : s • x = s • y) :
    x = y := by
  have hs' : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hs
  rw [← algebraMap_smul K s x, ← algebraMap_smul K s y] at h
  exact smul_right_injective _ hs' h

end Generic

section Extension

variable {A : Type v} [CommRing A] [Algebra R A] (B : Subalgebra R (K ⊗[R] A))
  {D : Type w} [CommRing D] [Algebra R D] [Module.Flat R D]

/-- Two algebra maps out of a subalgebra of the generic fibre into a flat algebra agree
when they agree on the elements `1 ⊗ a` that lie in the subalgebra. -/
theorem algHom_ext (g₁ g₂ : B →ₐ[R] D)
    (h : ∀ (a : A) (ha : (1 : K) ⊗ₜ a ∈ B), g₁ ⟨_, ha⟩ = g₂ ⟨_, ha⟩) : g₁ = g₂ := by
  ext b
  obtain ⟨s, a, hs, hsa⟩ := exists_smul_eq_one_tmul K A (b : K ⊗[R] A)
  have ha : (1 : K) ⊗ₜ a ∈ B := hsa ▸ B.smul_mem b.2 s
  have hb : s • b = ⟨_, ha⟩ := Subtype.ext hsa
  have h1 : s • g₁ b = s • g₂ b := by
    rw [← map_smul, ← map_smul, hb, h a ha]
  exact smul_right_injective D hs h1

variable {B}

omit [Module.Flat R D] in
/-- The generic extension of `f` maps `B` into the image of `D`. -/
theorem map_mem_range (f : A →ₐ[R] D)
    (hf : ∀ (a : A) (s : R), s ≠ 0 → (∃ b ∈ B, s • b = (1 : K) ⊗ₜ a) →
      ∃ d : D, f a = s • d)
    (b : B) :
    (Algebra.TensorProduct.map (AlgHom.id K K) f) (b : K ⊗[R] A) ∈
      (Algebra.TensorProduct.includeRight : D →ₐ[R] K ⊗[R] D).range := by
  obtain ⟨s, a, hs, hsa⟩ := exists_smul_eq_one_tmul K A (b : K ⊗[R] A)
  obtain ⟨d, hd⟩ := hf a s hs ⟨b, b.2, hsa⟩
  refine ⟨d, smul_left_cancel K D hs ?_⟩
  change s • ((1 : K) ⊗ₜ d) = s • (Algebra.TensorProduct.map (AlgHom.id K K) f) (b : K ⊗[R] A)
  rw [← AlgHom.map_smul_of_tower, hsa, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hd,
    TensorProduct.tmul_smul]

/-- The extension of `f : A → D` to the subalgebra `B` of the generic fibre. -/
def extend (f : A →ₐ[R] D)
    (hf : ∀ (a : A) (s : R), s ≠ 0 → (∃ b ∈ B, s • b = (1 : K) ⊗ₜ a) →
      ∃ d : D, f a = s • d) :
    B →ₐ[R] D :=
  ((AlgEquiv.ofInjective _ (includeRight_injective_of_flat K D)).symm.toAlgHom).comp
    ((((Algebra.TensorProduct.map (AlgHom.id K K) f).restrictScalars R).comp
      B.val).codRestrict _ (map_mem_range f hf))

theorem includeRight_extend (f : A →ₐ[R] D)
    (hf : ∀ (a : A) (s : R), s ≠ 0 → (∃ b ∈ B, s • b = (1 : K) ⊗ₜ a) →
      ∃ d : D, f a = s • d) (b : B) :
    (1 : K) ⊗ₜ extend f hf b =
      (Algebra.TensorProduct.map (AlgHom.id K K) f) (b : K ⊗[R] A) := by
  have := (AlgEquiv.ofInjective _ (includeRight_injective_of_flat K D)).apply_symm_apply
    ⟨_, map_mem_range f hf b⟩
  exact congrArg Subtype.val this

theorem extend_apply (f : A →ₐ[R] D)
    (hf : ∀ (a : A) (s : R), s ≠ 0 → (∃ b ∈ B, s • b = (1 : K) ⊗ₜ a) →
      ∃ d : D, f a = s • d) (a : A) (ha : (1 : K) ⊗ₜ a ∈ B) :
    extend f hf ⟨_, ha⟩ = f a := by
  apply includeRight_injective_of_flat (R := R) K D
  change (1 : K) ⊗ₜ extend f hf ⟨_, ha⟩ = (1 : K) ⊗ₜ f a
  rw [includeRight_extend]
  simp

end Extension

end Langlands.GroupScheme.IntegralModel.Smoothening
