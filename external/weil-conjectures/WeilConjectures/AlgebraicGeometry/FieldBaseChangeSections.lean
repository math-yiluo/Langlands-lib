/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections

/-!
# Sections of a base change to an affine scheme over a field

Let `X` be a scheme over a field `k`, `R` a `k`-algebra and `π : X ×_k Spec R ⟶ X` the first
projection. For an affine open `W ⊆ X`, flat base change identifies the ring of sections of
`X ×_k Spec R` over `π⁻¹ W` with `Γ(X, W) ⊗_k R`.

## Main results

- `AlgebraicGeometry.exists_ringEquiv_tensor_app_preimage_fst`: the ring isomorphism
  `Γ(X, W) ⊗_k R ≃ Γ(X ×_k Spec R, π⁻¹ W)`, `a ⊗ r ↦ π^♯ a · pr^♯ r`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- **Sections of a base change over the preimage of an affine open.** Let `X` be a scheme over a
field `k`, `R` a `k`-algebra and `W ⊆ X` an affine open. Then the ring of sections of
`X ×_k Spec R` over the preimage `π⁻¹ W` of `W` under the first projection is
`Γ(X, W) ⊗_k R`, via `a ⊗ r ↦ π^♯ a · pr^♯ r` (flat base change,
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`). Here `Γ(X, W)` is a
`k`-algebra via the structure morphism. -/
theorem exists_ringEquiv_tensor_app_preimage_fst {k R : Type u} [Field k] [CommRing R]
    [Algebra k R] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) :=
      ((sX.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
    ∃ e : Γ(X, W) ⊗[k] R ≃+* Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k R))),
        pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⁻¹ᵁ W),
      (∀ a, e (a ⊗ₜ 1) =
        (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app W a) ∧
      ∀ r, e (1 ⊗ₜ r) = (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k R)))).appLE ⊤
        _ le_top ((Scheme.ΓSpecIso (.of R)).inv r) := by
  let : Algebra k Γ(X, W) :=
    ((sX.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  set sU := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have : Flat sU := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have hUY :
      pullback.fst sX sU ⁻¹ᵁ W = pullback.fst sX sU ⁻¹ᵁ W ⊓ pullback.snd sX sU ⁻¹ᵁ ⊤ := by
    simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback sX sU) (US := ⊤) (UT := ⊤) (UX := W) le_top le_top hUY
    (isAffineOpen_top _) (isAffineOpen_top _) hW.isCompact hW.isQuasiSeparated
  have hpush := ((isIso_pushoutSection_iff _ _ _ _).mp hiso).flip
  have h := hpush.of_iso (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of R)) (Iso.refl _)
    (Iso.refl _) (f' := CommRingCat.ofHom (algebraMap k R))
    (g' := CommRingCat.ofHom (algebraMap k Γ(X, W)))
    (inl' := (Scheme.ΓSpecIso (.of R)).inv ≫ (pullback.snd sX sU).appLE ⊤ _ le_top)
    (inr' := (pullback.fst sX sU).appLE W _ le_rfl) ?_ ?_ ?_ ?_
  · refine ⟨h.tensorEquiv rfl rfl, fun a ↦ ?_, fun r ↦ ?_⟩
    · rw [h.tensorEquiv_tmul, map_one, mul_one, Scheme.Hom.app_eq_appLE]
    · rw [h.tensorEquiv_tmul, map_one, one_mul]
      rfl
  · rw [Scheme.Hom.appLE_top_top_eq_appTop, Scheme.ΓSpecIso_naturality]
  · ext x
    simp [RingHom.algebraMap_toAlgebra]
  · simp
  · simp

end AlgebraicGeometry
