/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor

/-!
# The points of a Kummer cover

The Kummer cover `𝒯_f = Y ×_{Spec Γ(Y)} Spec Γ(Y)[T₀]/(T₀ⁿ - f)` of a global function `f` on a
scheme `Y` (`AlgebraicGeometry.Scheme.kummerCover`) is the scheme of `n`-th roots of `f`: for a
`Y`-scheme `h : T ⟶ Y`, the `Y`-morphisms `T ⟶ 𝒯_f` are the global functions `w` on `T` with
`wⁿ = h^* f` (`AlgebraicGeometry.Scheme.kummerCoverHomEquiv`).

## Main definitions

- `AlgebraicGeometry.Scheme.homSpecEquiv`: `(T ⟶ Spec R) ≃ (R ⟶ Γ(T, ⊤))`.
- `AlgebraicGeometry.Scheme.kummerCoverHomEquiv`: the `Y`-points of `𝒯_f` are the `n`-th roots
  of `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry.Scheme

/-- Morphisms of schemes `T ⟶ Spec R` are ring maps `R ⟶ Γ(T, ⊤)`, through the `Γ`-`Spec`
adjunction. -/
noncomputable def homSpecEquiv (T : Scheme.{u}) (R : CommRingCat.{u}) :
    (T ⟶ Spec R) ≃ (R ⟶ Γ(T, ⊤)) :=
  (ΓSpec.adjunction.homEquiv T (op R)).symm.trans Quiver.Hom.opEquiv.symm

lemma homSpecEquiv_comp_specMap {T : Scheme.{u}} {R R' : CommRingCat.{u}} (g : T ⟶ Spec R)
    (φ : R' ⟶ R) : homSpecEquiv T R' (g ≫ Spec.map φ) = φ ≫ homSpecEquiv T R g := by
  simp only [homSpecEquiv, Equiv.trans_apply]
  change ((ΓSpec.adjunction.homEquiv T (op R')).symm (g ≫ Scheme.Spec.map φ.op)).unop = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  rfl

lemma homSpecEquiv_comp_toSpecΓ {T Y : Scheme.{u}} (h : T ⟶ Y) :
    homSpecEquiv T Γ(Y, ⊤) (h ≫ Y.toSpecΓ) = h.appTop := by
  have h₁ : (ΓSpec.adjunction.homEquiv Y (op Γ(Y, ⊤))).symm Y.toSpecΓ = 𝟙 _ := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have h₂ : (ΓSpec.adjunction.homEquiv T (op Γ(Y, ⊤))).symm (h ≫ Y.toSpecΓ) = Γ.rightOp.map h := by
    rw [Adjunction.homEquiv_naturality_left_symm, h₁, Category.comp_id]
  simp only [homSpecEquiv, Equiv.trans_apply]
  erw [h₂]
  rfl

variable {Y T : Scheme.{u}} (n : ℕ) (f : Γ(Y, ⊤)) (h : T ⟶ Y)

/-- The ring maps `Γ(Y)[T₀]/(T₀ⁿ - f) ⟶ Γ(T)` over `h^* : Γ(Y) ⟶ Γ(T)` are the `n`-th roots of
`h^* f`: the image of `T₀`. -/
noncomputable def kummerAlgebraHomEquiv :
    {ψ : CommRingCat.of (KummerAlgebra Y n f) ⟶ Γ(T, ⊤) //
        CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f)) ≫ ψ = h.appTop} ≃
      {w : Γ(T, ⊤) // w ^ n = h.appTop f} where
  toFun ψ := ⟨ψ.1 (AdjoinRoot.root _), by
    have hr : (AdjoinRoot.root (X ^ n - C f) : KummerAlgebra Y n f) ^ n =
        algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f) f := by
      have := AdjoinRoot.eval₂_root (X ^ n - C f)
      simpa [sub_eq_zero] using this
    rw [← map_pow, hr]
    exact congr($(ψ.2).hom f)⟩
  invFun w := ⟨CommRingCat.ofHom (AdjoinRoot.lift h.appTop.hom w.1 (by simp [w.2])), by
    ext x
    simp [AdjoinRoot.algebraMap_eq]⟩
  left_inv ψ := by
    apply Subtype.ext
    ext1
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext x
      have := congr($(ψ.2).hom x)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AdjoinRoot.algebraMap_eq] at this ⊢
      rw [AdjoinRoot.lift_of]
      exact this.symm
    · dsimp only
      rw [CommRingCat.hom_ofHom, AdjoinRoot.lift_root]
  right_inv w := by
    apply Subtype.ext
    dsimp only
    exact AdjoinRoot.lift_root (f := X ^ n - C f) (i := h.appTop.hom) (a := w.1) (by simp [w.2])

/-- The `Y`-morphisms `T ⟶ 𝒯_f` are the morphisms `T ⟶ Spec Γ(Y)[T₀]/(T₀ⁿ - f)` compatible with
`h` over `Spec Γ(Y)`, by the universal property of the pullback `𝒯_f`. -/
noncomputable def kummerCoverHomEquivSpec :
    {g : T ⟶ Y.kummerCover n f // g ≫ Y.kummerCoverπ n f = h} ≃
      {g : T ⟶ Spec (.of (KummerAlgebra Y n f)) //
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f))) =
          h ≫ Y.toSpecΓ} where
  toFun g := ⟨g.1 ≫ pullback.snd _ _, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, g.2]⟩
  invFun g := ⟨pullback.lift h g.1 g.2.symm, pullback.lift_fst _ _ _⟩
  left_inv g := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; exact g.2.symm
    · simp
  right_inv g := by
    apply Subtype.ext
    simp

/-- Morphisms `T ⟶ Spec Γ(Y)[T₀]/(T₀ⁿ - f)` compatible with `h` over `Spec Γ(Y)` are ring maps
`Γ(Y)[T₀]/(T₀ⁿ - f) ⟶ Γ(T)` over `h^*`. -/
noncomputable def specHomEquivKummerAlgebraHom :
    {g : T ⟶ Spec (.of (KummerAlgebra Y n f)) //
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f))) =
          h ≫ Y.toSpecΓ} ≃
      {ψ : CommRingCat.of (KummerAlgebra Y n f) ⟶ Γ(T, ⊤) //
        CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f)) ≫ ψ = h.appTop} where
  toFun g := ⟨homSpecEquiv T _ g.1, by
    rw [← homSpecEquiv_comp_specMap, g.2]; exact homSpecEquiv_comp_toSpecΓ h⟩
  invFun ψ := ⟨(homSpecEquiv T _).symm ψ.1, by
    apply (homSpecEquiv T _).injective
    rw [homSpecEquiv_comp_specMap, Equiv.apply_symm_apply, ψ.2]
    exact (homSpecEquiv_comp_toSpecΓ h).symm⟩
  left_inv g := Subtype.ext ((homSpecEquiv T _).symm_apply_apply g.1)
  right_inv ψ := Subtype.ext ((homSpecEquiv T _).apply_symm_apply ψ.1)

/-- Blueprint `def-pur-affine-line-datum` (torsor form): the Kummer cover `𝒯_f` of a global
function `f` on `Y` is the scheme of `n`-th roots of `f`: for `h : T ⟶ Y`, the morphisms
`T ⟶ 𝒯_f` over `Y` correspond to the global functions `w` on `T` with `wⁿ = h^* f`, by
`g ↦ g^* T₀`. -/
noncomputable def kummerCoverHomEquiv :
    {g : T ⟶ Y.kummerCover n f // g ≫ Y.kummerCoverπ n f = h} ≃
      {w : Γ(T, ⊤) // w ^ n = h.appTop f} :=
  (kummerCoverHomEquivSpec n f h).trans
    ((specHomEquivKummerAlgebraHom n f h).trans (kummerAlgebraHomEquiv n f h))

end AlgebraicGeometry.Scheme
