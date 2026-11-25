/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# Spreading out equalities of morphisms into a scheme locally of finite type

Let `f g : X ⟶ Y` be two `S`-morphisms, with `Y` locally of finite type over `S`. If `f` and `g`
agree on `Spec 𝒪_{X, x}`, then they agree on an open neighbourhood of `x`
(`AlgebraicGeometry.spread_out_unique_of_locallyOfFiniteType`). Unlike
`AlgebraicGeometry.spread_out_unique_of_isGermInjective'`, no condition on `X` is needed: on an
affine open `V ∋ f x` the ring `Γ(Y, V)` is generated over `Γ(S, W)` by finitely many sections, and
each of them has the same image under `f` and `g` near `x`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `f g : X ⟶ Y` be two `S`-morphisms with `Y` locally of finite type over `S`. If `f` and
`g` agree on `Spec 𝒪_{X, x}`, then they agree on an open neighbourhood of `x` (Stacks 01ZC
specialised to a single point). -/
lemma spread_out_unique_of_locallyOfFiniteType (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (f g : X ⟶ Y) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX) {x : X}
    (e : X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  have hfx : f x = g x := by simpa using congr($e (IsLocalRing.closedPoint _))
  have H : f.stalkMap x =
      Y.presheaf.stalkSpecializes (Inseparable.of_eq hfx.symm).specializes ≫ g.stalkMap x := by
    apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk _)]
    simpa [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  -- affine opens `W ∋ sX x`, `V ∋ f x` and `U₀ ∋ x`
  obtain ⟨_, ⟨W : S.Opens, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (sX x)) isOpen_univ
  have hfxW : f x ∈ sY ⁻¹ᵁ W := by
    change sY (f x) ∈ W
    rwa [← Scheme.Hom.comp_apply, hf]
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hxV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hfxW (sY ⁻¹ᵁ W).isOpen
  have hgxV : g x ∈ V := hfx ▸ hxV
  obtain ⟨_, ⟨U₀ : X.Opens, hU₀, rfl⟩, hxU₀, hU₀V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V from
      ⟨hxV, hgxV⟩) (f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V).isOpen
  have hU₀f : U₀ ≤ f ⁻¹ᵁ V := fun _ h ↦ (hU₀V h).1
  have hU₀g : U₀ ≤ g ⁻¹ᵁ V := fun _ h ↦ (hU₀V h).2
  have hVW' : V ≤ sY ⁻¹ᵁ W := hVW
  -- `Γ(Y, V)` is of finite type over `Γ(S, W)`
  have hft : RingHom.FiniteType (sY.appLE W V hVW').hom :=
    HasRingHomProperty.appLE @LocallyOfFiniteType sY ‹_› ⟨W, hW⟩ ⟨V, hV⟩ hVW'
  let := (sY.appLE W V hVW').hom.toAlgebra
  obtain ⟨s, hs⟩ := hft
  -- `f` and `g` agree on the germs at `x`
  have hgerm : f.appLE V U₀ hU₀f ≫ X.presheaf.germ U₀ x hxU₀ =
      g.appLE V U₀ hU₀g ≫ X.presheaf.germ U₀ x hxU₀ := by
    simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res', ← Scheme.Hom.germ_stalkMap,
      H]
    simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  choose W' hxW' i₁ i₂ hW' using fun b : Γ(Y, V) ↦
    X.presheaf.germ_eq x hxU₀ hxU₀ ((f.appLE V U₀ hU₀f) b) ((g.appLE V U₀ hU₀g) b)
      (by rw [← CommRingCat.comp_apply, hgerm, CommRingCat.comp_apply])
  let U : X.Opens := U₀ ⊓ s.inf W'
  have hxU : x ∈ U := by
    refine ⟨hxU₀, ?_⟩
    rw [Opens.coe_finset_inf]
    simpa using fun b _ ↦ hxW' b
  have hUU₀ : U ≤ U₀ := inf_le_left
  have hUW : U ≤ sX ⁻¹ᵁ W := by
    intro y hy
    have h := hVW (hU₀f (hUU₀ hy))
    change sY (f y) ∈ W at h
    change sX y ∈ W
    rwa [← Scheme.Hom.comp_apply, hf] at h
  refine ⟨U, hxU, ?_⟩
  -- the two maps `Γ(Y, V) ⟶ Γ(X, U)` agree
  have happ : f.appLE V U (hUU₀.trans hU₀f) = g.appLE V U (hUU₀.trans hU₀g) := by
    let := (sX.appLE W U hUW).hom.toAlgebra
    have hcf : sY.appLE W V hVW' ≫ f.appLE V U (hUU₀.trans hU₀f) = sX.appLE W U hUW := by
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [hf]
    have hcg : sY.appLE W V hVW' ≫ g.appLE V U (hUU₀.trans hU₀g) = sX.appLE W U hUW := by
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [hg]
    let φf : Γ(Y, V) →ₐ[Γ(S, W)] Γ(X, U) :=
      { (f.appLE V U (hUU₀.trans hU₀f)).hom with
        commutes' := fun r ↦ by
          change _ = (sX.appLE W U hUW) r
          rw [← hcf]
          rfl }
    let φg : Γ(Y, V) →ₐ[Γ(S, W)] Γ(X, U) :=
      { (g.appLE V U (hUU₀.trans hU₀g)).hom with
        commutes' := fun r ↦ by
          change _ = (sX.appLE W U hUW) r
          rw [← hcg]
          rfl }
    have hφ : φf = φg := by
      refine AlgHom.ext_of_adjoin_eq_top hs fun b hb ↦ ?_
      have hle : U ≤ W' b := inf_le_right.trans (Finset.inf_le hb)
      have h := congr(X.presheaf.map (homOfLE hle).op $(hW' b))
      simp only [← CommRingCat.comp_apply,
        Scheme.Hom.appLE_map] at h
      exact h
    ext b
    exact congr($hφ b)
  rw [← Scheme.Hom.resLE_comp_ι _ (hUU₀.trans hU₀f), ← Scheme.Hom.resLE_comp_ι _ (hUU₀.trans hU₀g)]
  congr 1
  have : IsAffine V := hV
  rw [← cancel_mono V.toScheme.isoSpec.hom]
  simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_naturality, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.resLE_appLE]
  congr 2
  have key : ∀ (U' : X.Opens) (V' : Y.Opens) (_ : U = U') (_ : V = V') (h₁ : U' ≤ f ⁻¹ᵁ V')
      (h₂ : U' ≤ g ⁻¹ᵁ V'), f.appLE V' U' h₁ = g.appLE V' U' h₂ := by
    rintro _ _ rfl rfl _ _
    exact happ
  exact key _ _ (by simp) (by simp) _ _

end AlgebraicGeometry
