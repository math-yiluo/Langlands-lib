import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Reductive.StarActionContinuityProof
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The quadratic extension cut out by an outer star action

For actual Tits index data `d` of a group over `K`, the absolute Galois
elements acting trivially on the simple vertices form a subgroup, the star
kernel. It is open by the proved continuity of the star action, hence closed,
and its fixed field in the separable closure is the field of definition of the
star action. When the star image consists of the identity and one nontrivial
permutation, the star kernel has index two, so the fixed field is a separable
quadratic extension; its nontrivial automorphism is the restriction of every
Galois element acting through the nontrivial permutation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The star kernel: absolute Galois elements whose star action fixes every
simple vertex. -/
def starKernel : Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) where
  carrier := {σ | ∀ a, d.star σ a = a}
  one_mem' := fun a => d.star_one a
  mul_mem' := by
    intro σ τ hσ hτ a
    rw [d.star_mul, hτ a, hσ a]
  inv_mem' := by
    intro σ hσ a
    have h := hσ (d.star σ⁻¹ a)
    rw [← d.star_mul, mul_inv_cancel, d.star_one] at h
    exact h.symm

theorem mem_starKernel_iff (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    σ ∈ d.starKernel ↔ ∀ a, d.star σ a = a :=
  Iff.rfl

/-- The star kernel contains the fixer of a finite subextension, by the proved
continuity of the star action, so it is open in the Krull topology. -/
theorem starKernel_isOpen : IsOpen (d.starKernel : Set (SeparableClosure K ≃ₐ[K]
    SeparableClosure K)) := by
  obtain ⟨L, hL, hfix⟩ := starActionContinuity K (SeparableClosure K) G d.pinning
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_ L.fixingSubgroup_isOpen
  intro σ hσ a
  have h1 := (hfix σ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ)).2
  apply Subtype.ext
  change (d.pinning.starAction σ).val.indexEquiv a.val = a.val
  rw [h1]
  rfl

theorem starKernel_isClosed : IsClosed (d.starKernel : Set (SeparableClosure K ≃ₐ[K]
    SeparableClosure K)) :=
  Subgroup.isClosed_of_isOpen _ d.starKernel_isOpen

/-- The field of definition of the star action: the fixed field of the star
kernel in the separable closure. -/
def starField : IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField d.starKernel

theorem starField_fixingSubgroup : d.starField.fixingSubgroup = d.starKernel :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨d.starKernel, d.starKernel_isClosed⟩

/-- An absolute Galois element fixes the star field pointwise exactly when its
star action is trivial. -/
theorem fixes_starField_iff (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (∀ x ∈ d.starField, σ x = x) ↔ ∀ a, d.star σ a = a := by
  rw [← IntermediateField.mem_fixingSubgroup_iff, d.starField_fixingSubgroup]
  rfl

/-- The star field lies in the separable closure, so it is separable over `K`. -/
theorem isSeparable_starField : Algebra.IsSeparable K d.starField :=
  inferInstance

theorem finrank_starField :
    Module.finrank K d.starField = d.starKernel.index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, d.starField_fixingSubgroup]

variable {d}

/-- Two Galois elements acting through the same permutation of a numbering
differ by an element of the star kernel. -/
theorem mul_inv_mem_starKernel {n : ℕ} {e : d.Vertex ≃ Fin n} {τ : Equiv.Perm (Fin n)}
    {σ ρ : SeparableClosure K ≃ₐ[K] SeparableClosure K}
    (hσ : ∀ a, e (d.star σ a) = τ (e a)) (hρ : ∀ a, e (d.star ρ a) = τ (e a)) :
    σ * ρ⁻¹ ∈ d.starKernel := by
  intro a
  have hy : d.star ρ (d.star ρ⁻¹ a) = a := by
    rw [← d.star_mul, mul_inv_cancel, d.star_one]
  rw [d.star_mul]
  apply e.injective
  rw [hσ, ← hρ, hy]

/-- Under a star image pair, a Galois element lies outside the star kernel
exactly when it acts through the nontrivial permutation. -/
theorem StarImagePair.not_mem_starKernel_iff {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    σ ∉ d.starKernel ↔ ∀ a, e (d.star σ a) = τ (e a) := by
  obtain ⟨hne, hdich, -⟩ := h
  constructor
  · intro hσ
    rcases hdich σ with h1 | h1
    · exact absurd (fun a => e.injective (h1 a)) hσ
    · exact h1
  · intro hσ hmem
    apply hne
    apply Equiv.ext
    intro i
    obtain ⟨a, rfl⟩ := e.surjective i
    rw [← hσ a, hmem a]
    rfl

/-- Under a star image pair, the star kernel has index two. -/
theorem StarImagePair.starKernel_index {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ) : d.starKernel.index = 2 := by
  obtain ⟨σ₀, hσ₀⟩ := h.2.2
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨σ₀⁻¹, fun hmem => ?_, fun b => ?_⟩
  · exact (h.not_mem_starKernel_iff σ₀).2 hσ₀ (by simpa using d.starKernel.inv_mem hmem)
  · by_cases hb : b ∈ d.starKernel
    · exact Or.inr hb
    · exact Or.inl (mul_inv_mem_starKernel ((h.not_mem_starKernel_iff b).1 hb) hσ₀)

theorem StarImagePair.finrank_starField {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ) :
    Module.finrank K d.starField = 2 := by
  rw [d.finrank_starField, h.starKernel_index]

theorem StarImagePair.isQuadraticExtension {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ) :
    Algebra.IsQuadraticExtension K d.starField :=
  ⟨h.finrank_starField⟩

theorem StarImagePair.isGalois {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ) : IsGalois K d.starField := by
  have hnormal : d.starKernel.Normal := Subgroup.normal_of_index_eq_two h.starKernel_index
  rw [← InfiniteGalois.normal_iff_isGalois, d.starField_fixingSubgroup]
  exact hnormal

/-- Every Galois element acting through the nontrivial permutation restricts on
the star field to the nonidentity automorphism of this separable quadratic
extension. -/
theorem StarImagePair.restrict_eq_conjugation {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hσ : ∀ a, e (d.star σ a) = τ (e a)) (x : d.starField) :
    haveI := h.isQuadraticExtension
    σ (x : SeparableClosure K) = (SU3Root.conjugation K d.starField x : SeparableClosure K) := by
  have := h.isQuadraticExtension
  have := h.isGalois
  have hne : σ.restrictNormal d.starField ≠ 1 := by
    intro h1
    apply (h.not_mem_starKernel_iff σ).2 hσ
    rw [d.mem_starKernel_iff, ← d.fixes_starField_iff σ]
    intro y hy
    have := AlgEquiv.restrictNormal_commutes σ d.starField ⟨y, hy⟩
    rw [h1] at this
    exact this.symm
  rw [← SU3Root.conjugation_unique K d.starField _ hne]
  exact (AlgEquiv.restrictNormal_commutes σ d.starField x).symm

/-- The separable quadratic extension attached to a star image pair: a
quadratic Galois subextension of the separable closure whose pointwise fixers
are exactly the Galois elements with trivial star action. -/
theorem StarImagePair.exists_quadraticField {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ) :
    ∃ F : IntermediateField K (SeparableClosure K),
      Module.finrank K F = 2 ∧ IsGalois K F ∧
        ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
          (∀ x ∈ F, σ x = x) ↔ ∀ a, d.star σ a = a :=
  ⟨d.starField, h.finrank_starField, h.isGalois, d.fixes_starField_iff⟩

end TitsIndexData

end Langlands.GroupScheme
