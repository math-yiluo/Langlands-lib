/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition comparisons determined by smooth counits

Source: the composite-adjunction argument in the current blueprint proof of
proposition-compatibility-purity-composition (blueprint: lem-pur-composition-counit-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory

namespace CategoryTheory.Adjunction

/-- A transitivity equation for the explicit counits implies composition of their
counit-preserving comparisons with any specified right adjoints.

Source: sk-prop-sp-composition.proof.md, tensor maps and the composite adjunction
(blueprint: lem-pur-composition-counit-comparison).

Proof. Transpose into the specified composite right adjoint. Naturality of the
first explicit counit moves the second comparison through it. The defining counit
equations of the two right-adjoint uniqueness isomorphisms then replace the two
specified counits by the explicit ones. The hypothesis identifies this map with
the explicit composite counit. The mate equation for the support compositor and
injectivity of the final adjunction Hom equivalence give the result. -/
theorem comparison_comp_of_counit
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {Jf Rf : D ⥤ C} {Jg Rg : E ⥤ D} {Jh Rh : E ⥤ C}
    (af : F ⊣ Jf) (ag : G ⊣ Jg) (ah : H ⊣ Jh)
    (bf : F ⊣ Rf) (bg : G ⊣ Rg) (bh : H ⊣ Rh)
    (alpha : F ⋙ G ≅ H) (K : E)
    (s : Jh.obj K ⟶ Jf.obj (Jg.obj K))
    (hs : alpha.hom.app (Jh.obj K) ≫ ah.counit.app K =
      G.map (F.map s) ≫ G.map (af.counit.app (Jg.obj K)) ≫ ag.counit.app K) :
    (ah.rightAdjointUniq bh).hom.app K =
      s ≫ Jf.map ((ag.rightAdjointUniq bg).hom.app K) ≫
        (af.rightAdjointUniq bf).hom.app (Rg.obj K) ≫
        (conjugateIsoEquiv (bf.comp bg) bh alpha.symm).hom.app K := by
  let q := (ag.rightAdjointUniq bg).hom.app K
  let r := s ≫ Jf.map q ≫ (af.rightAdjointUniq bf).hom.app (Rg.obj K)
  have hr : (F ⋙ G).map r ≫ (bf.comp bg).counit.app K =
      G.map (F.map s) ≫ G.map (af.counit.app (Jg.obj K)) ≫ ag.counit.app K := by
    have hf : F.map r ≫ bf.counit.app (Rg.obj K) =
        F.map s ≫ af.counit.app (Jg.obj K) ≫ q := by
      simp only [r, Functor.map_comp, Category.assoc,
        rightAdjointUniq_hom_app_counit]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ F.map s ≫ z) (af.counit_naturality q)
    simpa only [Functor.comp_map, comp_counit_app, Functor.map_comp,
      Category.assoc, q, rightAdjointUniq_hom_app_counit] using
      congrArg (fun z ↦ G.map z ≫ bg.counit.app K) hf
  apply (bh.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, rightAdjointUniq_hom_app_counit]
  calc
    ah.counit.app K =
        H.map r ≫ H.map ((conjugateIsoEquiv (bf.comp bg) bh alpha.symm).hom.app K) ≫
          bh.counit.app K := by
      rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
      change ah.counit.app K = H.map r ≫
        alpha.symm.hom.app (Rf.obj (Rg.obj K)) ≫ (bf.comp bg).counit.app K
      rw [alpha.symm.hom.naturality_assoc r, hr, ← hs]
      simp
    _ = _ := by simp only [r, q, Functor.map_comp, Category.assoc]


end CategoryTheory.Adjunction
