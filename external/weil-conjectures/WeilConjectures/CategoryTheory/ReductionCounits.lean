/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Reduction of right adjoints by transposition of the counit

Source: current blueprint proposition-sp-tower-geometric, final transition paragraph.
(blueprint: lem-sp-reduction-counits-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆
open CategoryTheory
namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {Cn : Type u₃} [Category.{v₃} Cn] {Dn : Type u₄} [Category.{v₄} Dn]
  {Cm : Type u₅} [Category.{v₅} Cm] {Dm : Type u₆} [Category.{v₆} Dm]
  {Fn : Cn ⥤ Dn} {Gn : Dn ⥤ Cn} (an : Fn ⊣ Gn)
  {Fm : Cm ⥤ Dm} {Gm : Dm ⥤ Cm} (am : Fm ⊣ Gm)
  (SX : Cn ⥤ Cm) (SY : Dn ⥤ Dm) (b : SX ⋙ Fm ≅ Fn ⋙ SY)

/-- The specified coefficient comparison is the transpose of the scalar-reduced counit.
Source: blueprint lemma-sp-reduction, displayed counit mate.
(blueprint: lem-sp-reduction-counits-adjunction) -/
def coefficientCounitMate (K : Dn) : SX.obj (Gn.obj K) ⟶ Gm.obj (SY.obj K) :=
  am.homEquiv _ _ (b.hom.app (Gn.obj K) ≫ SY.map (an.counit.app K))

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (Xn : C ⥤ Cn) (Yn : D ⥤ Dn) (Xm : C ⥤ Cm) (Ym : D ⥤ Dm)
  (en : F ⋙ Yn ≅ Xn ⋙ Fn) (em : F ⋙ Ym ≅ Xm ⋙ Fm)
  (rn : G ⋙ Xn ≅ Yn ⋙ Gn) (rm : G ⋙ Xm ≅ Ym ⋙ Gm)
  (rX : Xn ⋙ SX ⟶ Xm) (rY : Yn ⋙ SY ⟶ Ym)
  (hn : ∀ K : D, en.inv.app (G.obj K) ≫ Yn.map (adj.counit.app K) =
    Fn.map (rn.hom.app K) ≫ an.counit.app (Yn.obj K))
  (hm : ∀ K : D, em.inv.app (G.obj K) ≫ Ym.map (adj.counit.app K) =
    Fm.map (rm.hom.app K) ≫ am.counit.app (Ym.obj K))
  (hs : ∀ M : C,
    SY.map (en.inv.app M) ≫ rY.app (F.obj M) ≫ em.hom.app M =
      b.inv.app (Xn.obj M) ≫ Fm.map (rX.app M))

include adj en em hn hm hs

/-- Naturality of the tower counit forces the actual coefficient-reduction formula.
Source: blueprint proposition-sp-tower-geometric, final paragraph, including equal levels.
Proof: apply the inverse finite adjunction bijection at the lower level. The support
reduction square and naturality of the actual reduction at the tower counit rewrite
the left transpose as the scalar-reduced upper counit after the compact-support
comparison. On the right, counit naturality and the defining mate equation give
the same map, by naturality of the support comparison. Injectivity of the bijection
proves equality. No normalized-tower or coefficient-flatness hypothesis is used.
(blueprint: lem-sp-reduction-counits-adjunction) -/
theorem reductionCounits (K : D) :
    rX.app (G.obj K) ≫ rm.hom.app K =
      SX.map (rn.hom.app K) ≫ coefficientCounitMate an am SX SY b (Yn.obj K) ≫
        Gm.map (rY.app K) := by
  have hsupport (M : C) :
      Fm.map (rX.app M) ≫ em.inv.app M =
        b.hom.app (Xn.obj M) ≫ SY.map (en.inv.app M) ≫ rY.app (F.obj M) := by
    calc
      Fm.map (rX.app M) ≫ em.inv.app M =
          b.hom.app (Xn.obj M) ≫
            (b.inv.app (Xn.obj M) ≫ Fm.map (rX.app M)) ≫ em.inv.app M := by
              simp
      _ = b.hom.app (Xn.obj M) ≫
          (SY.map (en.inv.app M) ≫ rY.app (F.obj M) ≫ em.hom.app M) ≫
            em.inv.app M := by rw [hs M]
      _ = _ := by
        simp
  apply (am.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Fm.map_comp, Category.assoc]
  rw [← hm K, ← Category.assoc, hsupport (G.obj K)]
  simp only [Category.assoc]
  have hr := rY.naturality (adj.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hr
  rw [← hr]
  change b.hom.app (Xn.obj (G.obj K)) ≫ SY.map (en.inv.app (G.obj K)) ≫
      SY.map (Yn.map (adj.counit.app K)) ≫ rY.app K = _
  rw [← SY.map_comp_assoc, hn K, SY.map_comp]
  have hcm := am.counit.naturality (rY.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hcm
  rw [hcm]
  simp only [← Category.assoc]
  have hmate :
      Fm.map (coefficientCounitMate an am SX SY b (Yn.obj K)) ≫
          am.counit.app ((Yn ⋙ SY).obj K) =
        b.hom.app (Gn.obj (Yn.obj K)) ≫ SY.map (an.counit.app (Yn.obj K)) :=
    by simpa only [Functor.comp_obj, Functor.id_obj, coefficientCounitMate,
        Adjunction.homEquiv_counit] using
      (am.homEquiv _ _).symm_apply_apply
        (b.hom.app (Gn.obj (Yn.obj K)) ≫ SY.map (an.counit.app (Yn.obj K)))
  simp only [Category.assoc]
  have hb := b.hom.naturality (rn.hom.app K)
  change Fm.map (SX.map (rn.hom.app K)) ≫ b.hom.app (Gn.obj (Yn.obj K)) =
    b.hom.app (Xn.obj (G.obj K)) ≫ SY.map (Fn.map (rn.hom.app K)) at hb
  have he := congrArg
    (fun z ↦ Fm.map (SX.map (rn.hom.app K)) ≫ z ≫ rY.app K) hmate
  simp only [← Category.assoc] at he
  rw [hb] at he
  simpa only [Category.assoc] using he.symm

end CategoryTheory
