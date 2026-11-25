/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Yoneda

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

/-- Source: Stacks Project, Categories 0B65, applied after transporting adjunctions
across equivalences (the transport in Topologies 04HR).
Proof: let alpha be the inverse mate. For any x and z, choose z0 and an
isomorphism H(z0) to z. Full faithfulness of H, the first adjunction, full
faithfulness of G, beta at z0, and the second adjunction give successive
bijections from Hom(H(L1(x)), z) to Hom(L2(G(x)), z). The mate unit equation
and naturality of beta identify the resulting function with precomposition
by alpha at x. This function is bijective for every z. Taking z equal to
L2(G(x)) supplies a left inverse of alpha; injectivity with z equal to
H(L1(x)) then proves the other inverse equation. Each component of alpha
is therefore invertible, so alpha is a natural isomorphism.
(blueprint: lem-stage3-inverse-mate-equivalences) -/
theorem isIso_inverseMate_of_equivalences
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} [G.IsEquivalence] [H.IsEquivalence]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (beta : R₁ ⋙ G ≅ H ⋙ R₂) :
    IsIso (((mateEquiv adj₁ adj₂).symm beta.hom)) := by
  classical
  let alpha := ((mateEquiv adj₁ adj₂).symm beta.hom)
  let gff := Functor.FullyFaithful.ofFullyFaithful G
  let hff := Functor.FullyFaithful.ofFullyFaithful H
  have component (x : C) : IsIso (alpha.app x) := by
    apply isIso_of_coyoneda_map_bijective
    intro z
    let z₀ := H.inv.obj z
    let e : H.obj z₀ ≅ z := H.asEquivalence.counitIso.app z
    let eqv := (Iso.homCongr (Iso.refl (H.obj (L₁.obj x))) e.symm).trans
      (hff.homEquiv.symm.trans ((adj₁.homEquiv x z₀).trans
        (gff.homEquiv.trans ((Iso.homCongr (Iso.refl (G.obj x)) (beta.app z₀)).trans
          ((Iso.homCongr (Iso.refl (G.obj x)) (R₂.mapIso e)).trans
            (adj₂.homEquiv (G.obj x) z).symm)))))
    convert! eqv.bijective using 1
    ext f
    apply (adj₂.homEquiv (G.obj x) z).injective
    dsimp [eqv]
    simp only [Equiv.apply_symm_apply]
    rw [adj₂.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    have hu := unit_mateEquiv_symm adj₁ adj₂ beta.hom x
    change G.map (adj₁.unit.app x) ≫ beta.hom.app (L₁.obj x) =
      adj₂.unit.app (G.obj x) ≫ R₂.map (alpha.app x) at hu
    rw [← hu]
    dsimp [Iso.homCongr, Functor.FullyFaithful.homEquiv]
    simp only [Category.id_comp]
    simp only [Adjunction.homEquiv_unit, G.map_comp, Category.assoc]
    have hn := beta.hom.naturality (hff.preimage (f ≫ e.inv))
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [hff.map_preimage, ← R₂.map_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact NatIso.isIso_of_isIso_app alpha

end CategoryTheory
