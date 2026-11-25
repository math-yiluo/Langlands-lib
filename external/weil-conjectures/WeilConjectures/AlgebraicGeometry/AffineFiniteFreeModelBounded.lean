/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelComplex

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The explicit affine finite-free model is supported in degrees `[-r, 0]`.
Source: Stacks Project, Tag 068C, extension-by-zero support calculation
(blueprint: lem-affine-finite-free-model-bounded).

The extension along `n ↦ -n` is zero in positive degrees and below `-r`; the
inverse localized-site equivalence preserves zero objects. This is a direct
termwise calculation from the definition of `affineFiniteFreeModelComplex`. -/
theorem affine_finite_free_model_bounded {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) (r : ℕ)
    (hzero : ∀ n, r < n → IsZero (K.X n)) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((affineFiniteFreeModelComplex U hU K).X n) := by
  refine ⟨-(r : ℤ), 0, ?_⟩
  intro n hn
  dsimp [affineFiniteFreeModelComplex]
  change IsZero ((Scheme.Modules.overEquiv U).inverse.obj
    (((((tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat).X n))
  apply Functor.map_isZero
  rcases hn with hn | hn
  · let L := ((tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K
    have hi : ComplexShape.embeddingDownNat.f (-n).toNat = n := by
      simp only [ComplexShape.embeddingDownNat_f]
      omega
    apply IsZero.of_iso (Y := L.X (-n).toNat) _
      (L.extendXIso ComplexShape.embeddingDownNat hi)
    change IsZero ((tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj (K.X (-n).toNat))
    apply Functor.map_isZero
    exact hzero _ (by omega)
  · apply HomologicalComplex.isZero_extend_X
    intro i hi
    simp only [ComplexShape.embeddingDownNat_f] at hi
    omega

end AlgebraicGeometry
