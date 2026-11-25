/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction

/-!

# The mate of a base-change square under a change of coefficients, for named base changes

`CategoryTheory.Adjunction.map_mateEquiv_app_comp` takes its compatibility hypothesis in terms of
the components of the base-change isomorphisms `σ` and `σ'`. When these isomorphisms are built
from named morphisms `s` and `s'` (e.g. `asIso s`), the compatibility is usually proved about `s`
and `s'`. Matching `σ.hom.app M` with `s.app M` inside that hypothesis can then be very expensive
for the elaborator. `CategoryTheory.Adjunction.map_mateEquiv_app_comp_of_hom_eq` takes the
compatibility about `s` and `s'`, together with the equalities `σ.hom = s` and `σ'.hom = s'` of
natural transformations.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace CategoryTheory

variable {C₂ : Type u₁} {CC : Type u₂} {CF : Type u₃} {CX : Type u₄}
  [Category.{v₁} C₂] [Category.{v₂} CC] [Category.{v₃} CF] [Category.{v₄} CX]
  {C₂' : Type u₅} {CC' : Type u₆} {CF' : Type u₇} {CX' : Type u₈}
  [Category.{v₅} C₂'] [Category.{v₆} CC'] [Category.{v₇} CF'] [Category.{v₈} CX']
  {cL : CC ⥤ C₂} {cR : C₂ ⥤ CC} (a : cL ⊣ cR) {dL : CF ⥤ CX} {dR : CX ⥤ CF}
  (g : dL ⊣ dR) (ι : CC ⥤ CF) (Δ : C₂ ⥤ CX) (σ : cL ⋙ Δ ≅ ι ⋙ dL)
  {cL' : CC' ⥤ C₂'} {cR' : C₂' ⥤ CC'} (a' : cL' ⊣ cR') {dL' : CF' ⥤ CX'} {dR' : CX' ⥤ CF'}
  (g' : dL' ⊣ dR') (ι' : CC' ⥤ CF') (Δ' : C₂' ⥤ CX') (σ' : cL' ⋙ Δ' ≅ ι' ⋙ dL')
  (T₂ : C₂ ⥤ C₂') (TC : CC ⥤ CC') (TF : CF ⥤ CF') (TX : CX ⥤ CX')
  (τc : cL ⋙ T₂ ≅ TC ⋙ cL') (τd : dL ⋙ TX ≅ TF ⋙ dL')
  (τι : ι ⋙ TF ≅ TC ⋙ ι') (τΔ : Δ ⋙ TX ≅ T₂ ⋙ Δ')

/-- `CategoryTheory.Adjunction.map_mateEquiv_app_comp` with the compatibility of the base-change
isomorphisms `σ`, `σ'` stated for natural transformations `s = σ.hom` and `s' = σ'.hom`. -/
theorem Adjunction.map_mateEquiv_app_comp_of_hom_eq {s : cL ⋙ Δ ⟶ ι ⋙ dL} (hs : σ.hom = s)
    {s' : cL' ⋙ Δ' ⟶ ι' ⋙ dL'} (hs' : σ'.hom = s')
    (hσ : ∀ M : CC, TX.map (s.app M) ≫ τd.hom.app (ι.obj M) ≫ dL'.map (τι.hom.app M) =
      τΔ.hom.app (cL.obj M) ≫ Δ'.map (τc.hom.app M) ≫ s'.app (TC.obj M)) (P : C₂) :
    TF.map ((mateEquiv a g (TwoSquare.mk _ _ _ _ σ.inv)).app P) ≫
        (mateEquiv g g' (TwoSquare.mk _ _ _ _ τd.inv)).app (Δ.obj P) ≫
          dR'.map (τΔ.hom.app P) =
      τι.hom.app (cR.obj P) ≫
        ι'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ τc.inv)).app P) ≫
          (mateEquiv a' g' (TwoSquare.mk _ _ _ _ σ'.inv)).app (T₂.obj P) := by
  subst hs hs'
  exact Adjunction.map_mateEquiv_app_comp a g ι Δ σ a' g' ι' Δ' σ' T₂ TC TF TX τc τd τι τΔ hσ P

end CategoryTheory
