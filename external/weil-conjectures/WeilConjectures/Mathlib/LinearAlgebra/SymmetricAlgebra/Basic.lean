/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Basic

/-!
# The symmetric algebra commutes with localization

Let `S` be a submonoid of `R`, `R'` a localization of `R` at `S` and `g : M →ₗ[R] N` a
localization of the `R`-module `M` at `S`, with `N` an `R'`-module. Then the natural map
`Sym_R M ⟶ Sym_{R'} N` is a localization at (the image of) `S`
(`SymmetricAlgebra.isLocalization_mapOfLocalization`). This is the algebraic input for the
symmetric algebra `Sym^• ℰ` of a quasi-coherent sheaf `ℰ` to be a quasi-coherent algebra: on
affine opens its sections are `Sym_{Γ(U)} Γ(U, ℰ)`, compatibly with restriction to basic opens.
-/

@[expose] public section

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R']
  [IsLocalization S R'] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N]
  [Module R N] [Module R' N] [IsScalarTower R R' N] (g : M →ₗ[R] N)

/-- The map `Sym_R M ⟶ Sym_{R'} N` induced by `g : M →ₗ[R] N`. -/
noncomputable def mapOfLocalization : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R' N :=
  lift ((ι R' N).restrictScalars R ∘ₗ g)

omit [IsLocalization S R'] in
@[simp]
lemma mapOfLocalization_ι (m : M) :
    mapOfLocalization R' g (ι R M m) = ι R' N (g m) := by
  simp [mapOfLocalization]

/-- **The symmetric algebra commutes with localization.** If `R'` is the localization of `R` at
`S` and `g : M →ₗ[R] N` is a localization of modules at `S` (`N` an `R'`-module), then
`Sym_{R'} N` is the localization of `Sym_R M` at the image of `S`. -/
theorem isLocalization_mapOfLocalization [IsLocalizedModule S g] :
    letI := (mapOfLocalization R' g).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (SymmetricAlgebra R M) S)
      (SymmetricAlgebra R' N) := by
  let := (mapOfLocalization R' g).toRingHom.toAlgebra
  have halg (x : SymmetricAlgebra R M) :
      algebraMap (SymmetricAlgebra R M) (SymmetricAlgebra R' N) x = mapOfLocalization R' g x :=
    rfl
  set φ := mapOfLocalization R' g
  have hφ (r : R) : φ (algebraMap R _ r) = algebraMap R (SymmetricAlgebra R' N) r := φ.commutes r
  have hR (r : R) : algebraMap R (SymmetricAlgebra R' N) r =
      algebraMap R' (SymmetricAlgebra R' N) (algebraMap R R' r) :=
    IsScalarTower.algebraMap_apply R R' _ r
  constructor
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [halg, hφ, hR]
    exact (IsLocalization.map_units R' ⟨s, hs⟩).map _
  · -- every element is a fraction `φ x / φ s`
    suffices H : ∀ z : SymmetricAlgebra R' N, ∃ x : SymmetricAlgebra R M, ∃ s ∈ S,
        z * algebraMap R _ s = φ x by
      intro z
      obtain ⟨x, s, hs, h⟩ := H z
      exact ⟨⟨x, ⟨_, s, hs, rfl⟩⟩, by simpa [halg, hφ] using h⟩
    intro z
    induction z using SymmetricAlgebra.induction with
    | algebraMap r =>
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj S r
      refine ⟨algebraMap R _ a, s, s.2, ?_⟩
      rw [hφ, hR, hR, ← map_mul, h]
    | ι n =>
      obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj S g n
      refine ⟨ι R M m, s, s.2, ?_⟩
      rw [mapOfLocalization_ι, ← h, mul_comm, ← Algebra.smul_def, LinearMap.map_smul_of_tower]
      rfl
    | mul a b ha hb =>
      obtain ⟨x, s, hs, hx⟩ := ha
      obtain ⟨y, t, ht, hy⟩ := hb
      refine ⟨x * y, s * t, S.mul_mem hs ht, ?_⟩
      rw [map_mul, map_mul, ← hx, ← hy]
      ring
    | add a b ha hb =>
      obtain ⟨x, s, hs, hx⟩ := ha
      obtain ⟨y, t, ht, hy⟩ := hb
      refine ⟨x * algebraMap R _ t + y * algebraMap R _ s, s * t, S.mul_mem hs ht, ?_⟩
      simp only [map_add, map_mul, hφ]
      rw [← hx, ← hy]
      ring
  · -- injectivity up to `S`: construct the inverse map into the localization
    intro x y hxy
    let T := Algebra.algebraMapSubmonoid (SymmetricAlgebra R M) S
    let L := Localization T
    have hu (s : S) : IsUnit (algebraMap R L s) := by
      rw [IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) L]
      exact IsLocalization.map_units L (⟨_, s, s.2, rfl⟩ : T)
    let : Algebra R' L := (IsLocalization.lift (M := S) (S := R') hu).toAlgebra
    have : IsScalarTower R R' L := .of_algebraMap_eq fun r ↦
      (IsLocalization.lift_eq (M := S) (S := R') hu r).symm
    let h₀ : M →ₗ[R] L :=
      (IsScalarTower.toAlgHom R (SymmetricAlgebra R M) L).toLinearMap ∘ₗ ι R M
    let h₁ : N →ₗ[R] L := IsLocalizedModule.lift S g h₀ fun s ↦ by
      rw [Module.End.isUnit_iff]
      obtain ⟨u, hu'⟩ := hu s
      refine ⟨fun a b h ↦ (hu s).mul_left_cancel ?_, fun b ↦ ⟨(↑u⁻¹ : L) * b, ?_⟩⟩
      · simpa [Algebra.smul_def] using h
      · simp [Algebra.smul_def, ← hu']
    let h₂ : N →ₗ[R'] L := h₁.extendScalarsOfIsLocalization S R'
    let ψ : SymmetricAlgebra R' N →ₐ[R'] L := lift h₂
    have hψ : (ψ.restrictScalars R).comp φ =
        IsScalarTower.toAlgHom R (SymmetricAlgebra R M) L := by
      apply algHom_ext
      ext m
      simp [ψ, h₂, h₁, h₀, φ]
    have := congr(ψ $hxy)
    have hx := congr($hψ x)
    have hy := congr($hψ y)
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hx hy
    rw [halg, halg, hx, hy] at this
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := T) this
    exact ⟨c, hc⟩

end SymmetricAlgebra
