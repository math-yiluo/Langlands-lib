/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Flat base change of global sections

Let `S` and `T` be affine schemes, `f : T ⟶ S` flat and `h : X ⟶ S` with `X` quasi-compact and
quasi-separated. Then the square of global sections of the cartesian square `X ×_S T` is a
pushout of rings, i.e. `Γ(X ×_S T) = Γ(X) ⊗_{Γ(S)} Γ(T)`. This is a repackaging of
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S T X : Scheme.{u}} [IsAffine S] [IsAffine T] (f : T ⟶ S) [Flat f] (h : X ⟶ S)
  [CompactSpace X] [QuasiSeparatedSpace X]

lemma Scheme.Hom.appLE_top_top_eq_appTop {X Y : Scheme.{u}} (g : X ⟶ Y)
    (e : ⊤ ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ e = g.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

/-- **Flat base change of global sections**: for `S`, `T` affine, `f : T ⟶ S` flat and `X` a
quasi-compact quasi-separated `S`-scheme, the global sections of `X ×_S T` form the pushout
`Γ(X) ⊗_{Γ(S)} Γ(T)`. -/
theorem isPushout_appTop_of_flat :
    IsPushout h.appTop f.appTop (pullback.fst h f).appTop (pullback.snd h f).appTop := by
  have H : IsIso (pushoutSection (IsPullback.of_hasPullback h f) (US := ⊤) (UT := ⊤) (UX := ⊤)
      le_top le_top (UY := ⊤) (by simp)) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ (isAffineOpen_top S)
      (isAffineOpen_top T) CompactSpace.isCompact_univ
      (isQuasiSeparated_univ_iff.mpr inferInstance)
  have := (isIso_pushoutSection_iff _ _ _ _).mp H
  simpa only [Scheme.Hom.appLE_top_top_eq_appTop] using this

section TensorEquiv

open TensorProduct

variable {R A' E Q : CommRingCat.{u}} {φ : R ⟶ E} {α : R ⟶ A'} {i₁ : E ⟶ Q} {i₂ : A' ⟶ Q}
  [Algebra R A'] [Algebra R E]

/-- A pushout square of rings identifies `Q` with the tensor product `A' ⊗[R] E`, given that the
algebra structures are the ones induced by the span. -/
noncomputable def _root_.CategoryTheory.IsPushout.tensorEquiv (h : IsPushout φ α i₁ i₂)
    (hα : CommRingCat.ofHom (algebraMap R A') = α) (hφ : CommRingCat.ofHom (algebraMap R E) = φ) :
    A' ⊗[R] E ≃+* Q := by
  have h' : IsPushout α φ
      (CommRingCat.ofHom (S := A' ⊗[R] E) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := A' ⊗[R] E) Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← hα, ← hφ]
    exact CommRingCat.isPushout_tensorProduct R A' E
  exact (h'.isoIsPushout _ _ h.flip).commRingCatIsoToRingEquiv

lemma _root_.CategoryTheory.IsPushout.tensorEquiv_tmul (h : IsPushout φ α i₁ i₂)
    (hα : CommRingCat.ofHom (algebraMap R A') = α) (hφ : CommRingCat.ofHom (algebraMap R E) = φ)
    (a : A') (x : E) : h.tensorEquiv hα hφ (a ⊗ₜ x) = i₂ a * i₁ x := by
  have h' : IsPushout α φ
      (CommRingCat.ofHom (S := A' ⊗[R] E) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := A' ⊗[R] E) Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← hα, ← hφ]
    exact CommRingCat.isPushout_tensorProduct R A' E
  have e₁ := h'.inl_isoIsPushout_hom _ _ h.flip
  have e₂ := h'.inr_isoIsPushout_hom _ _ h.flip
  have : (a ⊗ₜ[R] x : A' ⊗[R] E) = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight x := by simp
  rw [IsPushout.tensorEquiv]
  change (h'.isoIsPushout _ _ h.flip).hom (a ⊗ₜ x) = _
  rw [this, map_mul]
  congr 1
  · exact congr($(e₁) a)
  · exact congr($(e₂) x)

end TensorEquiv

end AlgebraicGeometry
