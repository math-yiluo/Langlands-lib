/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing
public import WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent

/-!
# Morphisms of quasi-coherent modules on affine schemes

Morphisms out of a quasi-coherent module on an affine scheme `X` are determined by, and can be
built from, `Γ(X, ⊤)`-linear maps on global sections. This is deduced from the case of `Spec R`
by pushing forward along the isomorphism `X ⟶ Spec Γ(X, ⊤)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]

omit [N.IsQuasicoherent] in
/-- Morphisms out of a quasi-coherent module on an affine scheme are determined by their effect
on global sections. -/
lemma hom_ext_of_isAffine {α β : M ⟶ N} (h : ∀ m : Γ(M, ⊤), α.app ⊤ m = β.app ⊤ m) :
    α = β := by
  have := isQuasicoherent_pushforward_of_isAffineHom X.toSpecΓ M
  apply (pushforward X.toSpecΓ).map_injective
  exact hom_ext_of_isQuasicoherent_Spec h

/-- A `Γ(X, ⊤)`-linear map between the global sections of quasi-coherent modules on an affine
scheme comes from a morphism of modules. -/
lemma exists_hom_app_top_eq_of_isAffine (χ : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = χ m := by
  have := isQuasicoherent_pushforward_of_isAffineHom X.toSpecΓ M
  have := isQuasicoherent_pushforward_of_isAffineHom X.toSpecΓ N
  obtain ⟨φ', hφ'⟩ := exists_hom_app_top_eq' (M := (pushforward X.toSpecΓ).obj M)
    (N := (pushforward X.toSpecΓ).obj N) χ.toAddMonoidHom fun a m ↦ by
      have key (P : X.Modules) (x : Γ((pushforward X.toSpecΓ).obj P, ⊤)) :
          ((ΓSpecIso Γ(X, ⊤)).inv ≫ (Spec Γ(X, ⊤)).presheaf.map
            (homOfLE (le_top : (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op).hom a • x =
            (a • (show Γ(P, ⊤) from x) : Γ(P, ⊤)) := by
        have h1 := congr(Hom.app
          $(pushforward_map_smulHom X.toSpecΓ P ((ΓSpecIso Γ(X, ⊤)).inv a)) ⊤ x)
        rw [pushforward_map_app, smulHom_app_apply] at h1
        refine h1.symm.trans ?_
        erw [smulHom_app_apply]
        have h2 : X.toSpecΓ.appTop ((ΓSpecIso Γ(X, ⊤)).inv a) = a := by
          rw [← CommRingCat.comp_apply, toSpecΓ_appTop, Iso.inv_hom_id]
          rfl
        rw [h2, show (homOfLE (le_top : X.toSpecΓ ⁻¹ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op = 𝟙 _
          from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
        rfl
      exact (congrArg χ (key M m)).trans ((χ.map_smul a m).trans (key N (χ m)).symm)
  refine ⟨(pushforward X.toSpecΓ).preimage φ', fun m ↦ ?_⟩
  have := congr(Hom.app $((pushforward X.toSpecΓ).map_preimage φ') ⊤ m)
  exact this.trans (hφ' m)

end AlgebraicGeometry.Scheme.Modules
