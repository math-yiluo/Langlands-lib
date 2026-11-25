/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# The isomorphism of invertible modules with the same transition functions

Let `U i` be an open cover of a scheme `X`, `e i` a free generator of an `𝒪_X`-module `M` on
`U i` and `f i` a free generator of `N` on `U i`, such that both families have the same
transition functions. Then there is a unique isomorphism `M ≅ N` sending each `e i` to `f i`
(`AlgebraicGeometry.Scheme.Modules.isoOfIsFreeGenerator`). This upgrades
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_isFreeGenerator` to an actual isomorphism,
characterised by its values on the generators.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} {U : ι → X.Opens}
  {e : ∀ i, Γ(M, U i)} {f : ∀ i, Γ(N, U i)}

/-- The transition condition for the families `e` and `f` of free generators is symmetric. -/
lemma transition_symm_of_isFreeGenerator (he : ∀ i, IsFreeGenerator (e i))
    (hf : ∀ i, IsFreeGenerator (f i))
    (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
      a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) →
        a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j))
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W))
    (hab : a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j)) :
    a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) := by
  have hj' := (he j).map hj
  have h := hc i j W hi hj a _ (hj'.coeff_smul _).symm
  rw [← hj'.coeff_smul (a • M.presheaf.map (homOfLE hi).op (e i))]
  congr 1
  exact ((hf j).map hj).smul_left_injective (h.symm.trans hab)

variable (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
  (hf : ∀ i, IsFreeGenerator (f i))
  (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
    a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) →
      a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j))

/-- **The isomorphism of invertible modules with the same transition functions.** Let `U i` be
an open cover of `X`, `e i` a free generator of `M` on `U i` and `f i` a free generator of `N` on
`U i`, such that `e i` and `e j` are related on every open of `U i ⊓ U j` in the same way as
`f i` and `f j`. This is the isomorphism `M ≅ N` sending each `e i` to `f i`
(`isoOfIsFreeGenerator_hom_app_smul`); it is obtained by gluing the local isomorphisms
`a • e i ↦ a • f i` (the sheaf axiom for `N`). -/
noncomputable def isoOfIsFreeGenerator : M ≅ N where
  hom := glueHom hU he hc
  inv := glueHom hU hf (transition_symm_of_isFreeGenerator he hf hc)
  hom_inv_id := by
    refine hom_ext _ _ fun V ↦ ?_
    ext m
    exact (isGlueValue_glueHom_app hU hf (transition_symm_of_isFreeGenerator he hf hc) _).unique
      hU hf ((isGlueValue_glueHom_app hU he hc m).symm he hf)
  inv_hom_id := by
    refine hom_ext _ _ fun V ↦ ?_
    ext m
    exact (isGlueValue_glueHom_app hU he hc _).unique hU he
      ((isGlueValue_glueHom_app hU hf (transition_symm_of_isFreeGenerator he hf hc) m).symm hf he)

/-- **Local description of `isoOfIsFreeGenerator`**: on an open `W ⊆ U i`, it sends
`a • e i|_W` to `a • f i|_W`. -/
lemma isoOfIsFreeGenerator_hom_app_smul (i : ι) {W : X.Opens} (hW : W ≤ U i) (a : Γ(X, W)) :
    (isoOfIsFreeGenerator hU he hf hc).hom.app W (a • M.presheaf.map (homOfLE hW).op (e i)) =
      a • N.presheaf.map (homOfLE hW).op (f i) := by
  have h := isGlueValue_glueHom_app hU he hc (a • M.presheaf.map (homOfLE hW).op (e i)) i W
    le_rfl hW a (by rw [presheaf_map_id_apply])
  rwa [presheaf_map_id_apply] at h

/-- **`isoOfIsFreeGenerator` sends `e i` to `f i`.** -/
lemma isoOfIsFreeGenerator_hom_app (i : ι) :
    (isoOfIsFreeGenerator hU he hf hc).hom.app (U i) (e i) = f i := by
  have h := isoOfIsFreeGenerator_hom_app_smul hU he hf hc i le_rfl 1
  rwa [one_smul, one_smul, presheaf_map_id_apply, presheaf_map_id_apply] at h

/-- **The inverse of `isoOfIsFreeGenerator` sends `f i` to `e i`.** -/
lemma isoOfIsFreeGenerator_inv_app (i : ι) :
    (isoOfIsFreeGenerator hU he hf hc).inv.app (U i) (f i) = e i := by
  rw [← isoOfIsFreeGenerator_hom_app hU he hf hc i, ← ConcreteCategory.comp_apply,
    ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
  rfl

section Tensor

open MonoidalCategory

variable {L₁ L₂ L₃ : X.Modules} {e₁ : ∀ i, Γ(L₁, U i)} {e₂ : ∀ i, Γ(L₂, U i)}
  {e₃ : ∀ i, Γ(L₃, U i)}

/-- **Multiplicative transition functions.** Let `e₁ i`, `e₂ i`, `e₃ i` be free generators of
`L₁`, `L₂`, `L₃` on `U i`. If on every open `W ⊆ U i ⊓ U j` the transition function of `e₃` is
the product of those of `e₁` and `e₂`, then the families `e₁ i ⊗ e₂ i` of `L₁ ⊗ L₂` and `e₃ i`
of `L₃` have the same transition functions, as required by `isoOfIsFreeGenerator`. -/
lemma tmulSection_transition_of_isFreeGenerator (he₁ : ∀ i, IsFreeGenerator (e₁ i))
    (he₂ : ∀ i, IsFreeGenerator (e₂ i))
    (h : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j), ∃ c d : Γ(X, W),
      c • L₁.presheaf.map (homOfLE hj).op (e₁ j) = L₁.presheaf.map (homOfLE hi).op (e₁ i) ∧
      d • L₂.presheaf.map (homOfLE hj).op (e₂ j) = L₂.presheaf.map (homOfLE hi).op (e₂ i) ∧
      (c * d) • L₃.presheaf.map (homOfLE hj).op (e₃ j) = L₃.presheaf.map (homOfLE hi).op (e₃ i))
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (α β : Γ(X, W))
    (hαβ : α • (L₁ ⊗ L₂).presheaf.map (homOfLE hi).op (tmulSection (e₁ i) (e₂ i)) =
      β • (L₁ ⊗ L₂).presheaf.map (homOfLE hj).op (tmulSection (e₁ j) (e₂ j))) :
    α • L₃.presheaf.map (homOfLE hi).op (e₃ i) = β • L₃.presheaf.map (homOfLE hj).op (e₃ j) := by
  obtain ⟨c, d, hc, hd, hcd⟩ := h i j W hi hj
  have hβ : α * (c * d) = β := by
    refine (((he₁ j).map hj).tmulSection ((he₂ j).map hj)).smul_left_injective ?_
    dsimp only
    rw [tmulSection_map, tmulSection_map, ← hc, ← hd, smul_tmulSection, tmulSection_smul,
      smul_smul] at hαβ
    rw [← hαβ, smul_smul, mul_assoc]
  rw [← hcd, smul_smul, hβ]

end Tensor

end AlgebraicGeometry.Scheme.Modules
