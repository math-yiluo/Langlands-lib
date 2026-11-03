import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Homogeneous bases of the augmentation cotangent space -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.TorusUnipotence

open DirectSum

section Augmentation

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k)

/-- The class in `I / I²` of `a - ε a`, where `I` is the kernel of the augmentation `ε`. -/
def cotangentMap : A →ₗ[k] (RingHom.ker ε).Cotangent where
  toFun a := (RingHom.ker ε).toCotangent ⟨a - algebraMap k A (ε a), by simp [RingHom.mem_ker]⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c a := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring

theorem cotangentMap_of_mem {a : A} (ha : a ∈ RingHom.ker ε) :
    cotangentMap ε a = (RingHom.ker ε).toCotangent ⟨a, ha⟩ := by
  have h : ε a = 0 := ha
  simp only [cotangentMap, LinearMap.coe_mk, AddHom.coe_mk, h, map_zero, sub_zero]

theorem cotangentMap_eq_iff {a b : A} (ha : a ∈ RingHom.ker ε) (hb : b ∈ RingHom.ker ε) :
    cotangentMap ε a = cotangentMap ε b ↔ a - b ∈ RingHom.ker ε ^ 2 := by
  rw [cotangentMap_of_mem ε ha, cotangentMap_of_mem ε hb, Ideal.toCotangent_eq]

theorem cotangentMap_eq_zero_iff {a : A} (ha : a ∈ RingHom.ker ε) :
    cotangentMap ε a = 0 ↔ a ∈ RingHom.ker ε ^ 2 := by
  rw [cotangentMap_of_mem ε ha, Ideal.toCotangent_eq_zero]

theorem cotangentMap_algebraMap (c : k) : cotangentMap ε (algebraMap k A c) = 0 := by
  simp only [cotangentMap, LinearMap.coe_mk, AddHom.coe_mk, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  exact map_zero _

theorem cotangentMap_mul (a b : A) :
    cotangentMap ε (a * b) = ε a • cotangentMap ε b + ε b • cotangentMap ε a := by
  have hI : ∀ x : A, x - algebraMap k A (ε x) ∈ RingHom.ker ε := fun x => by
    simp [RingHom.mem_ker]
  have hsq : (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) ∈ RingHom.ker ε ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (hI a) (hI b)
  have h0 := (cotangentMap_eq_zero_iff ε (Ideal.pow_le_self two_ne_zero hsq)).2 hsq
  have key : a * b = (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) + ε a • b +
      ε b • a - algebraMap k A (ε a * ε b) := by
    simp only [map_mul, Algebra.smul_def]
    ring
  rw [key, map_sub, map_add, map_add, h0, map_smul, map_smul, cotangentMap_algebraMap]
  abel

end Augmentation

section Graded

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
  {ι : Type*} [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule k A) [GradedAlgebra 𝒜]
  (ε : A →ₐ[k] k)

/-- A graded augmentation only sees the degree-zero component. -/
theorem augmentation_decompose_zero (hε : ∀ i : ι, i ≠ 0 → ∀ a ∈ 𝒜 i, ε a = 0) (a : A) :
    ε (decompose 𝒜 a 0 : A) = ε a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    rename_i i
    by_cases hi : i = 0
    · subst hi
      rw [decompose_of_mem_same 𝒜 a.2]
    · rw [decompose_of_mem_ne 𝒜 a.2 hi, map_zero, hε i hi a a.2]
  | add a b ha hb => rw [decompose_add, add_apply, Submodule.coe_add, map_add, map_add, ha, hb]

/-- If the degree-zero augmentation elements lie in the square of the augmentation ideal, the
cotangent classes of homogeneous elements of nonzero degree span the cotangent space. -/
theorem span_homogeneous_cotangent (hε : ∀ i : ι, i ≠ 0 → ∀ a ∈ 𝒜 i, ε a = 0)
    (hI0 : ∀ a ∈ 𝒜 0, ε a = 0 → a ∈ RingHom.ker ε ^ 2) :
    Submodule.span k {t | ∃ i : ι, i ≠ 0 ∧ ∃ a ∈ 𝒜 i, cotangentMap ε a = t} = ⊤ := by
  set T := {t | ∃ i : ι, i ≠ 0 ∧ ∃ a ∈ 𝒜 i, cotangentMap ε a = t}
  have key : ∀ a : A, cotangentMap ε a - cotangentMap ε (decompose 𝒜 a 0 : A) ∈
      Submodule.span k T := by
    intro a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous a =>
      rename_i i
      by_cases hi : i = 0
      · subst hi
        rw [decompose_of_mem_same 𝒜 a.2, sub_self]
        exact Submodule.zero_mem _
      · rw [decompose_of_mem_ne 𝒜 a.2 hi, map_zero, sub_zero]
        exact Submodule.subset_span ⟨i, hi, a, a.2, rfl⟩
    | add a b ha hb =>
      rw [decompose_add, add_apply, Submodule.coe_add, map_add, map_add, add_sub_add_comm]
      exact Submodule.add_mem _ ha hb
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨a, ha⟩, rfl⟩ := (RingHom.ker ε).toCotangent_surjective x
  rw [← cotangentMap_of_mem ε ha]
  have ha0 : (decompose 𝒜 a 0 : A) ∈ RingHom.ker ε := by
    have h : ε a = 0 := ha
    change ε _ = 0
    rw [augmentation_decompose_zero 𝒜 ε hε, h]
  have h0 : cotangentMap ε (decompose 𝒜 a 0 : A) = 0 :=
    (cotangentMap_eq_zero_iff ε ha0).2 (hI0 _ (decompose 𝒜 a 0).2 ha0)
  simpa [h0] using key a

/-- A basis of the augmentation cotangent space consisting of classes of homogeneous elements
of nonzero degree. -/
theorem exists_homogeneous_cotangent_basis (hε : ∀ i : ι, i ≠ 0 → ∀ a ∈ 𝒜 i, ε a = 0)
    (hI0 : ∀ a ∈ 𝒜 0, ε a = 0 → a ∈ RingHom.ker ε ^ 2) :
    ∃ (σ : Type v) (b : Module.Basis σ k (RingHom.ker ε).Cotangent) (z : σ → A) (w : σ → ι),
      (∀ s, w s ≠ 0) ∧ (∀ s, z s ∈ 𝒜 (w s)) ∧ ∀ s, cotangentMap ε (z s) = b s := by
  set T := {t | ∃ i : ι, i ≠ 0 ∧ ∃ a ∈ 𝒜 i, cotangentMap ε a = t}
  obtain ⟨B, hBT, hspan, hli⟩ := exists_linearIndependent k T
  have hsp : ⊤ ≤ Submodule.span k (Set.range ((↑) : B → (RingHom.ker ε).Cotangent)) := by
    rw [Subtype.range_coe, hspan, span_homogeneous_cotangent 𝒜 ε hε hI0]
  have hmem : ∀ t : B, ∃ i : ι, i ≠ 0 ∧ ∃ a ∈ 𝒜 i, cotangentMap ε a = t := fun t => hBT t.2
  choose w hw z hz hzt using hmem
  exact ⟨B, Module.Basis.mk hli hsp, z, w, hw, hz, fun s => by rw [Module.Basis.mk_apply, hzt]⟩

end Graded

end Langlands.GroupScheme.TorusUnipotence
