import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The ring pullback of an artinian colength-one extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.ArtinianColengthOne

variable {Λ A' : Type u} [CommRing Λ] [IsLocalRing Λ] [IsArtinianRing Λ]
  [CommRing A'] [Algebra Λ A']

omit [IsArtinianRing Λ] in
/-- If the cokernel of `Λ → A'` has length one, the maximal ideal of `Λ` multiplies `A'`
into the image of `Λ`. -/
theorem smul_mem_range
    (hlen : Module.length Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) = 1)
    {z : Λ} (hz : z ∈ IsLocalRing.maximalIdeal Λ) (x : A') :
    z • x ∈ LinearMap.range (Algebra.linearMap Λ A') := by
  have hs : IsSimpleModule Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) :=
    Module.length_eq_one_iff.mp hlen
  have heq := IsLocalRing.eq_maximalIdeal
    (IsSimpleModule.annihilator_isMaximal (R := Λ)
      (M := A' ⧸ LinearMap.range (Algebra.linearMap Λ A')))
  rw [← heq] at hz
  have h0 := (Module.mem_annihilator.mp hz) (Submodule.Quotient.mk x)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  exact h0

/-- If moreover `Λ → A'` is injective, an element `z` of the maximal ideal of `Λ` multiplies
`A'` into the image of the maximal ideal. -/
theorem exists_mem_maximalIdeal (hinj : Function.Injective (algebraMap Λ A'))
    (hlen : Module.length Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) = 1)
    {z : Λ} (hz : z ∈ IsLocalRing.maximalIdeal Λ) (x : A') :
    ∃ w ∈ IsLocalRing.maximalIdeal Λ, z • x = algebraMap Λ A' w := by
  obtain ⟨w, hw⟩ := smul_mem_range hlen hz x
  refine ⟨w, ?_, hw.symm⟩
  have : Nontrivial A' := hinj.nontrivial
  by_contra hw'
  have hu : IsUnit w := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hw'
    exact hw'
  have hu' : IsUnit (algebraMap Λ A' z * x) := by
    rw [← Algebra.smul_def, ← hw]
    exact hu.map (algebraMap Λ A')
  have hzn : IsNilpotent (algebraMap Λ A' z) :=
    (Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hz).map (algebraMap Λ A')
  exact hzn.not_isUnit (isUnit_of_mul_isUnit_left hu')

/-- Every element of the extended maximal ideal `m A'` is the image of an element of `m`. -/
theorem exists_of_mem_map (hinj : Function.Injective (algebraMap Λ A'))
    (hlen : Module.length Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) = 1)
    {y : A'} (hy : y ∈ (IsLocalRing.maximalIdeal Λ).map (algebraMap Λ A')) :
    ∃ w ∈ IsLocalRing.maximalIdeal Λ, y = algebraMap Λ A' w := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, zero_mem _, (map_zero _).symm⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, hw₁, rfl⟩ := h₁
    obtain ⟨w₂, hw₂, rfl⟩ := h₂
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, (map_add _ _ _).symm⟩
  | smul r y _ h =>
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨w', hw', he⟩ := exists_mem_maximalIdeal hinj hlen hw r
    refine ⟨w', hw', ?_⟩
    rw [← he, smul_eq_mul, Algebra.smul_def, mul_comm]

/-- The maximal ideal of a local artinian ring is nilpotent. -/
theorem isNilpotent_maximalIdeal : IsNilpotent (IsLocalRing.maximalIdeal Λ) := by
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := Λ)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

variable (Λ A')

omit [IsArtinianRing Λ] in
/-- The left inclusion `A' → A' ⊗[Λ] k` is surjective. -/
theorem includeLeft_surjective :
    Function.Surjective (Algebra.TensorProduct.includeLeft :
      A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ) := by
  intro c
  obtain ⟨y, hy⟩ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A'
    (IsLocalRing.maximalIdeal Λ)).surjective c
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨y, hy⟩

omit [IsArtinianRing Λ] in
/-- The kernel of `A' → A' ⊗[Λ] k` is the extended maximal ideal. -/
theorem ker_includeLeft :
    RingHom.ker (Algebra.TensorProduct.includeLeft :
      A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom =
      (IsLocalRing.maximalIdeal Λ).map (algebraMap Λ A') := by
  ext y
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A'
    (IsLocalRing.maximalIdeal Λ)).injective.eq_iff, map_zero]
  rfl

/-- The kernel of `A' → A' ⊗[Λ] k` is nilpotent. -/
theorem isNilpotent_ker_includeLeft :
    IsNilpotent (RingHom.ker (Algebra.TensorProduct.includeLeft :
      A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom) := by
  obtain ⟨n, hn⟩ := isNilpotent_maximalIdeal (Λ := Λ)
  refine ⟨n, ?_⟩
  rw [ker_includeLeft, ← Ideal.map_pow]
  change (IsLocalRing.maximalIdeal Λ ^ n).map (algebraMap Λ A') = ⊥
  rw [show IsLocalRing.maximalIdeal Λ ^ n = ⊥ from hn, Ideal.map_bot]

variable {Λ A'}

/-- `Λ` is the ring pullback `k ×_{A' ⊗[Λ] k} A'`. -/
theorem isPullback (hinj : Function.Injective (algebraMap Λ A'))
    (hlen : Module.length Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) = 1) :
    IsPullback (CommRingCat.ofHom (Algebra.ofId Λ (IsLocalRing.ResidueField Λ)).toRingHom)
      (CommRingCat.ofHom (Algebra.ofId Λ A').toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom) := by
  have hw : CommRingCat.ofHom (Algebra.ofId Λ (IsLocalRing.ResidueField Λ)).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom =
      CommRingCat.ofHom (Algebra.ofId Λ A').toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom := by
    ext x
    change (Algebra.TensorProduct.includeRight :
        IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ)
        (algebraMap Λ _ x) =
      (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ)
        (algebraMap Λ A' x)
    rw [AlgHom.commutes, AlgHom.commutes]
  let : ReflectsLimit
      (cospan (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom))
      (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  apply IsPullback.of_map (forget CommRingCat) hw
  rw [Types.isPullback_iff]
  refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hw], ?_, ?_⟩
  · rintro x y ⟨-, h⟩
    exact hinj h
  · intro c a' h
    change (Algebra.TensorProduct.includeRight :
        IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ) c =
      (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ) a' at h
    obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective c
    have hk : a' - algebraMap Λ A' x₀ ∈ RingHom.ker (Algebra.TensorProduct.includeLeft :
        A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ).toRingHom := by
      rw [RingHom.mem_ker]
      change (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ)
        (a' - algebraMap Λ A' x₀) = 0
      rw [map_sub, ← h, AlgHom.commutes]
      change (Algebra.TensorProduct.includeRight :
        IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ)
        (algebraMap Λ _ x₀) - _ = 0
      rw [AlgHom.commutes, sub_self]
    rw [ker_includeLeft] at hk
    obtain ⟨w, hw, he⟩ := exists_of_mem_map hinj hlen hk
    refine ⟨x₀ + w, ?_, ?_⟩
    · change IsLocalRing.residue Λ (x₀ + w) = IsLocalRing.residue Λ x₀
      rw [map_add, (IsLocalRing.residue_eq_zero_iff w).mpr hw, add_zero]
    · change algebraMap Λ A' (x₀ + w) = a'
      rw [map_add, ← he, add_sub_cancel]

end Langlands.AlgebraicGeometry.Picard.ArtinianColengthOne
